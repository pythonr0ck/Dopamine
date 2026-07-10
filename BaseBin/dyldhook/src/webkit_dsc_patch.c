#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>
#include <mach/mach.h>
#include <sys/mman.h>
#include <mach-o/loader.h>

#include "machomerger_hook.h"
#include "dyld_jbinfo.h"
#include "dyld.h"

typedef struct Loader Loader;
typedef struct LoadOptions LoadOptions;
typedef struct RuntimeState RuntimeState;

// ============================================================================
// DSC entry-point trampoline support
// ============================================================================

struct dsc_header {
    char        magic[16];
    uint32_t    mappingOffset;
    uint32_t    mappingCount;
    uint32_t    imagesOffsetOld;
    uint32_t    imagesCountOld;
    uint64_t    dyldBaseAddress;
    uint64_t    codeSignatureOffset;
    uint64_t    codeSignatureSize;
    uint64_t    slideInfoOffsetUnused;
    uint64_t    slideInfoSizeUnused;
    uint64_t    localSymbolsOffset;
    uint64_t    localSymbolsSize;
    uint8_t     uuid[16];
    uint64_t    cacheType;
    uint32_t    branchPoolsOffset;
    uint32_t    branchPoolsCount;
    uint64_t    dyldInCacheMH;
    uint64_t    dyldInCacheEntry;
    uint64_t    imagesTextOffset;
    uint64_t    imagesTextCount;
    uint64_t    patchInfoAddr;
    uint64_t    patchInfoSize;
    uint64_t    otherImageGroupAddrUnused;
    uint64_t    otherImageGroupSizeUnused;
    uint64_t    progClosuresAddr;
    uint64_t    progClosuresSize;
    uint64_t    progClosuresTrieAddr;
    uint64_t    progClosuresTrieSize;
    uint32_t    platform;
    uint32_t    formatBits;
    uint64_t    sharedRegionStart;
    uint64_t    sharedRegionSize;
    uint64_t    maxSlide;
};

#define DSC_IMAGES_OFFSET_FIELDOFF  0x1C0
#define DSC_IMAGES_COUNT_FIELDOFF   0x1C4

struct dsc_image_info {
    uint64_t    address;
    uint64_t    modTime;
    uint64_t    inode;
    uint32_t    pathFileOffset;
    uint32_t    pad;
};

struct dsc_patch_info_v2 {
    uint32_t    patchTableVersion;
    uint32_t    patchLocationVersion;
    uint64_t    patchTableArrayAddr;
    uint64_t    patchTableArrayCount;
    uint64_t    patchImageExportsArrayAddr;
    uint64_t    patchImageExportsArrayCount;
};

struct dsc_image_patches_v2 {
    uint32_t    patchClientsStartIndex;
    uint32_t    patchClientsCount;
    uint32_t    patchExportsStartIndex;
    uint32_t    patchExportsCount;
};

struct dsc_image_export_v2 {
    uint32_t    dylibOffsetOfImpl;
    uint32_t    exportNameOffsetAndKind;
};

struct DylibPatch {
    int64_t     overrideOffsetOfImpl;
};

#define DYLIBPATCH_END          ((int64_t)-1)
#define DYLIBPATCH_MISSING      ((int64_t)0)
#define DYLIBPATCH_OBJCCLASS    ((int64_t)1)
#define DYLIBPATCH_SINGLETON    ((int64_t)2)

static const void *gDyldCacheAddr = NULL;

static bool is_executable_dylib_offset(const void *slidMachHeader,
                                       uint64_t imageUnslidAddr,
                                       uint32_t dylibOffset)
{
    const struct mach_header_64 *mh = (const struct mach_header_64 *)slidMachHeader;
    if (mh->magic != MH_MAGIC_64)
        return false;

    const uint8_t *lc = (const uint8_t *)slidMachHeader + sizeof(struct mach_header_64);
    for (uint32_t i = 0; i < mh->ncmds; i++) {
        const struct load_command *cmd = (const struct load_command *)lc;
        if (cmd->cmd == LC_SEGMENT_64) {
            const struct segment_command_64 *seg = (const struct segment_command_64 *)lc;
            if (seg->initprot & VM_PROT_EXECUTE) {
                uint64_t segRelStart = seg->vmaddr - imageUnslidAddr;
                if (dylibOffset >= segRelStart &&
                    dylibOffset <  segRelStart + seg->vmsize)
                    return true;
            }
        }
        lc += cmd->cmdsize;
    }
    return false;
}

static void write_adrp_add_br_trampoline(void *dsc_func, void *override_func)
{
    uint64_t pc       = (uint64_t)dsc_func;
    uint64_t target   = (uint64_t)override_func;
    int64_t  adrpDelta = (int64_t)((target & ~0xFFFULL) - (pc & ~0xFFFULL));

    if (adrpDelta > 0x100000000LL || adrpDelta < -0x100000000LL)
        return;

    uint32_t immhi   = (uint32_t)((adrpDelta >> 9) & 0x00FFFFE0);
    uint32_t immlo   = (uint32_t)((adrpDelta << 17) & 0x60000000);
    uint32_t off12   = (uint32_t)(target & 0xFFF);

    uint32_t insn[3];
    insn[0] = 0x90000010 | immlo | immhi;
    insn[1] = 0x91000210 | (off12 << 10);
    insn[2] = 0xD61F0200;

    const uint64_t PAGE_MASK = ~0x3FFFULL;
    uintptr_t page_start = (uintptr_t)dsc_func & PAGE_MASK;
    uintptr_t page_end   = ((uintptr_t)dsc_func + 12 + 0x3FFF) & PAGE_MASK;
    size_t    region_len  = page_end - page_start;

    mach_port_t self_port = task_self_trap();
    kern_return_t kr = vm_protect(self_port, (vm_address_t)page_start,
                                  (vm_size_t)region_len, false,
                                  VM_PROT_READ | VM_PROT_WRITE | VM_PROT_COPY);
    if (kr != KERN_SUCCESS)
        return;

    volatile uint32_t *dst = (volatile uint32_t *)dsc_func;
    dst[0] = insn[0];
    dst[1] = insn[1];
    dst[2] = insn[2];

    vm_protect(self_port, (vm_address_t)page_start,
               (vm_size_t)region_len, false,
               VM_PROT_READ | VM_PROT_EXECUTE);

    __asm__ volatile (
        "dc cvau, %0\n"
        "dc cvau, %1\n"
        "dsb ish\n"
        "ic ivau, %0\n"
        "ic ivau, %1\n"
        "dsb ish\n"
        "isb\n"
        :: "r"((uintptr_t)dsc_func), "r"((uintptr_t)dsc_func + 8)
        : "memory"
    );
}

extern bool loader_overridesDylibInCache(const void *self, const struct DylibPatch **patchesOut, uint16_t *indexOut)
__asm__("_MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader21overridesDylibInCacheERPKNS0_10DylibPatchERt");
extern const void *loader_loadAddress(const void *self, void *state)
__asm__("_MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader11loadAddressERNS_12RuntimeStateE");

extern void ORIG(_ZNK5dyld46Loader17applyCachePatchesERNS_12RuntimeStateERNS_34DyldCacheDataConstLazyScopedWriterE)(const void *self, void *state, void *cacheDataConst);

void HOOK(_ZNK5dyld46Loader17applyCachePatchesERNS_12RuntimeStateERNS_34DyldCacheDataConstLazyScopedWriterE)(const void *self, void *state, void *cacheDataConst)
{
    ORIG(_ZNK5dyld46Loader17applyCachePatchesERNS_12RuntimeStateERNS_34DyldCacheDataConstLazyScopedWriterE)(self, state, cacheDataConst);

    const struct DylibPatch *patches = NULL;
    uint16_t overriddenIndex = 0;
    if (!loader_overridesDylibInCache(self, &patches, &overriddenIndex))
        return;
    if (!patches)
        return;
    if (!gDyldCacheAddr)
        return;

    const void *overrideBase = loader_loadAddress(self, state);
    if (!overrideBase)
        return;

    const struct dsc_header *hdr = (const struct dsc_header *)gDyldCacheAddr;
    int64_t slide = (int64_t)((intptr_t)gDyldCacheAddr - (intptr_t)hdr->sharedRegionStart);

    uint32_t imagesOffset = *(const uint32_t *)((const uint8_t *)hdr + DSC_IMAGES_OFFSET_FIELDOFF);
    const struct dsc_image_info *images = (const struct dsc_image_info *)((const uint8_t *)hdr + imagesOffset);
    uint64_t dscDylibBase = images[overriddenIndex].address + (uint64_t)slide;

    if (hdr->patchInfoAddr == 0 || hdr->patchInfoSize == 0)
        return;
    const struct dsc_patch_info_v2 *patchInfo =
    (const struct dsc_patch_info_v2 *)((uintptr_t)hdr->patchInfoAddr + slide);
    if (patchInfo->patchTableVersion < 2)
        return;

    const struct dsc_image_patches_v2 *imagePatches =
    (const struct dsc_image_patches_v2 *)((uintptr_t)patchInfo->patchTableArrayAddr + slide);
    const struct dsc_image_export_v2 *imageExports =
    (const struct dsc_image_export_v2 *)((uintptr_t)patchInfo->patchImageExportsArrayAddr + slide);

    const struct dsc_image_patches_v2 *imgPatch = &imagePatches[overriddenIndex];
    const struct DylibPatch *patchEntry = patches;

    uint64_t dscDylibUnslidBase = images[overriddenIndex].address;
    const void *dscDylibMachHeader = (const void *)dscDylibBase;

    for (uint32_t i = 0; i < imgPatch->patchExportsCount; i++, patchEntry++) {
        int64_t overrideOff = patchEntry->overrideOffsetOfImpl;

        if (overrideOff == DYLIBPATCH_END)
            break;
        if (overrideOff == DYLIBPATCH_MISSING ||
            overrideOff == DYLIBPATCH_OBJCCLASS ||
            overrideOff == DYLIBPATCH_SINGLETON)
            continue;

        const struct dsc_image_export_v2 *exp =
        &imageExports[imgPatch->patchExportsStartIndex + i];

        uint32_t patchKind = exp->exportNameOffsetAndKind >> 28;
        if (patchKind != 0)
            continue;

        if (!is_executable_dylib_offset(dscDylibMachHeader,
            dscDylibUnslidBase,
            exp->dylibOffsetOfImpl))
            continue;

        uintptr_t dscFuncAddr      = (uintptr_t)(dscDylibBase + exp->dylibOffsetOfImpl);
        uintptr_t overrideFuncAddr = (uintptr_t)overrideBase + (uintptr_t)((intptr_t)overrideOff);

        write_adrp_add_br_trampoline((void *)dscFuncAddr, (void *)overrideFuncAddr);
    }
}

extern bool ORIG(_ZNK5dyld413ProcessConfig9DyldCache17isOverridablePathEPKc)(const void *dyldCache, const char *dylibPath);
bool HOOK(_ZNK5dyld413ProcessConfig9DyldCache17isOverridablePathEPKc)(const void *dyldCache, const char *dylibPath)
{
    if (!gDyldCacheAddr && dyldCache) {
        gDyldCacheAddr = *(const void *const *)dyldCache;
    }
    (void)dylibPath;
    return true;
}

extern bool ORIG(_ZN5dyld413ProcessConfig9DyldCache23isAlwaysOverridablePathEPKc)(const char *dylibPath);
bool HOOK(_ZN5dyld413ProcessConfig9DyldCache23isAlwaysOverridablePathEPKc)(const char *dylibPath)
{
    (void)dylibPath;
    return true;
}

// ============================================================================
// matchesPath hook — prevent double-loading of jbroot overrides
// ============================================================================
extern bool ORIG(_ZNK5dyld416JustInTimeLoader11matchesPathEPKc)(const void *self, const char *path);
bool HOOK(_ZNK5dyld416JustInTimeLoader11matchesPathEPKc)(const void *self, const char *path)
{
    if (ORIG(_ZNK5dyld416JustInTimeLoader11matchesPathEPKc)(self, path))
        return true;

    if (path[0] == '/' && path[1] == 'v' && path[2] == 'a' && path[3] == 'r' && path[4] == '/') {
        char buf[PATH_MAX];
        strlcpy(buf, "/private", PATH_MAX);
        strlcat(buf, path, PATH_MAX);
        if (ORIG(_ZNK5dyld416JustInTimeLoader11matchesPathEPKc)(self, buf))
            return true;
    }

    if (strncmp(path, "/private/var/", 13) == 0) {
        if (ORIG(_ZNK5dyld416JustInTimeLoader11matchesPathEPKc)(self, path + 8))
            return true;
    }

    return false;
}

// ============================================================================
// Linker Dummy Stubs
// MachOMerger needs these symbols to exist during the initial clang linking
// phase. MachOMerger will overwrite these stubs with actual branches later.
// ============================================================================
__asm__(
".globl _MACHOMERGER_ORIG__ZNK5dyld416JustInTimeLoader11matchesPathEPKc\n"
"_MACHOMERGER_ORIG__ZNK5dyld416JustInTimeLoader11matchesPathEPKc:\n"
"    ret\n"

".globl _MACHOMERGER_ORIG__ZNK5dyld46Loader17applyCachePatchesERNS_12RuntimeStateERNS_34DyldCacheDataConstLazyScopedWriterE\n"
"_MACHOMERGER_ORIG__ZNK5dyld46Loader17applyCachePatchesERNS_12RuntimeStateERNS_34DyldCacheDataConstLazyScopedWriterE:\n"
"    ret\n"

".globl _MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader11loadAddressERNS_12RuntimeStateE\n"
"_MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader11loadAddressERNS_12RuntimeStateE:\n"
"    ret\n"

".globl _MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader21overridesDylibInCacheERPKNS0_10DylibPatchERt\n"
"_MACHOMERGER_TRAMPOLINE__ZNK5dyld46Loader21overridesDylibInCacheERPKNS0_10DylibPatchERt:\n"
"    ret\n"
);
