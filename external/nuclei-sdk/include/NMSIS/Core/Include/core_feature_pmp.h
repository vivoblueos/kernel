/*
 * Copyright (c) 2019 Nuclei Limited. All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the License); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef __CORE_FEATURE_PMP_H__
#define __CORE_FEATURE_PMP_H__
/*!
 * @file     core_feature_pmp.h
 * @brief    PMP feature API header file for Nuclei N/NX Core
 */
/*
 * PMP Feature Configuration Macro:
 * 1. __PMP_PRESENT:  Define whether Physical Memory Protection(PMP) is present or not
 *   * 0: Not present
 *   * 1: Present
 * 2. __PMP_ENTRY_NUM:  Define the number of PMP entries, only 8 or 16 is configurable.
 */
#ifdef __cplusplus
extern "C" {
#endif

#include "core_feature_base.h"
#include "core_compatiable.h"

#if defined(__PMP_PRESENT) && (__PMP_PRESENT == 1)
/* ===== PMP Operations ===== */
/**
 * \defgroup NMSIS_Core_PMP_Functions   PMP Functions
 * \ingroup  NMSIS_Core
 * \brief    Functions that related to the RISCV Phyiscal Memory Protection.
 * \details
 * Optional physical memory protection (PMP) unit provides per-hart machine-mode
 * control registers to allow physical memory access privileges (read, write, execute)
 * to be specified for each physical memory region.
 *
 * The PMP can supports region access control settings as small as four bytes.
 *
 *   @{
 */
#ifndef __PMP_ENTRY_NUM
/* numbers of PMP entries(__PMP_ENTRY_NUM) should be defined in <Device.h> */
#error "__PMP_ENTRY_NUM is not defined, please check!"
#endif

typedef struct PMP_CONFIG {
    /**
     * set locking bit, addressing mode, read, write, and instruction execution permissions,
     * see \ref PMP_L, \ref PMP_R, \ref PMP_W, \ref PMP_X, .etc in <riscv_encoding.h>
     */
    unsigned int protection;
    /**
     * Size of memory region as power of 2, it has to be minimum 2 and maxium \ref __RISCV_XLEN according to the
     * hard-wired granularity 2^N bytes, if N = 12, then order has to be at least 12; if not, the order read out
     * is N though you configure less than N.
     */
    unsigned long order;
    /**
     * Base address of memory region
     * It must be 2^order aligned address
     */
    unsigned long base_addr;
} pmp_config;

/**
 * \brief   Get PMPCFGx Register by csr index
 * \details Return the content of the PMPCFGx Register.
 * \param [in]    csr_idx    PMPCFG CSR index(0-3)
 * \return                   PMPCFGx Register value
 * \remark
 * - For RV64, only csr_idx = 0 and csr_idx = 2 is allowed.
 *   pmpcfg0 and pmpcfg2 hold the configurations
 *   for the 16 PMP entries, pmpcfg1 and pmpcfg3 are illegal
 * - For RV32, pmpcfg0–pmpcfg3, hold the configurations
 *   pmp0cfg–pmp15cfg for the 16 PMP entries
 */
__STATIC_INLINE rv_csr_t __get_PMPCFGx(uint32_t csr_idx)
{
    switch (csr_idx) {
        case 0: return __RV_CSR_READ(CSR_PMPCFG0);
        case 1: return __RV_CSR_READ(CSR_PMPCFG1);
        case 2: return __RV_CSR_READ(CSR_PMPCFG2);
        case 3: return __RV_CSR_READ(CSR_PMPCFG3);
        default: return 0;
    }
}

/**
 * \brief   Set PMPCFGx by csr index
 * \details Write the given value to the PMPCFGx Register.
 * \param [in]    csr_idx      PMPCFG CSR index(0-3)
 * \param [in]    pmpcfg       PMPCFGx Register value to set
 * \remark
 * - For RV64, only csr_idx = 0 and csr_idx = 2 is allowed.
 *   pmpcfg0 and pmpcfg2 hold the configurations
 *   for the 16 PMP entries, pmpcfg1 and pmpcfg3 are illegal
 * - For RV32, pmpcfg0–pmpcfg3, hold the configurations
 *   pmp0cfg–pmp15cfg for the 16 PMP entries
 */
__STATIC_INLINE void __set_PMPCFGx(uint32_t csr_idx, rv_csr_t pmpcfg)
{
    switch (csr_idx) {
        case 0: __RV_CSR_WRITE(CSR_PMPCFG0, pmpcfg); break;
        case 1: __RV_CSR_WRITE(CSR_PMPCFG1, pmpcfg); break;
        case 2: __RV_CSR_WRITE(CSR_PMPCFG2, pmpcfg); break;
        case 3: __RV_CSR_WRITE(CSR_PMPCFG3, pmpcfg); break;
        default: return;
    }
}

/**
 * \brief   Get 8bit PMPxCFG Register by PMP entry index
 * \details Return the content of the PMPxCFG Register.
 * \param [in]    entry_idx    PMP region index(0-15)
 * \return               PMPxCFG Register value
 */
__STATIC_INLINE uint8_t __get_PMPxCFG(uint32_t entry_idx)
{
    rv_csr_t pmpcfgx = 0;
    uint8_t csr_cfg_num = 0;
    uint16_t csr_idx = 0;
    uint16_t cfg_shift = 0;

    if (entry_idx >= __PMP_ENTRY_NUM) return 0;

#if __RISCV_XLEN == 32
    csr_cfg_num = 4;
    csr_idx = entry_idx >> 2;
#elif __RISCV_XLEN == 64
    csr_cfg_num = 8;
    /* For RV64, pmpcfg0 and pmpcfg2 each hold 8 PMP entries, align by 2 */
    csr_idx = (entry_idx >> 2) & ~1;
#else
    // TODO Add RV128 Handling
    return 0;
#endif
    pmpcfgx = __get_PMPCFGx(csr_idx);
    /*
     * first get specific pmpxcfg's order in one CSR composed of csr_cfg_num pmpxcfgs,
     * then get pmpxcfg's bit position in one CSR by left shift 3(each pmpxcfg size is one byte)
     */
    cfg_shift = (entry_idx & (csr_cfg_num - 1)) << 3;

    /* read specific pmpxcfg register value */
    return (uint8_t)(__RV_EXTRACT_FIELD(pmpcfgx, 0xFF << cfg_shift));
}

/**
 * \brief   Set 8bit PMPxCFG by pmp entry index
 * \details Set the given pmpxcfg value to the PMPxCFG Register.
 * \param [in]    entry_idx      PMPx region index(0-15)
 * \param [in]    pmpxcfg  PMPxCFG register value to set
 * \remark
 * - For RV32, 4 pmpxcfgs are densely packed into one CSR in order
 *   For RV64, 8 pmpxcfgs are densely packed into one CSR in order
 */
__STATIC_INLINE void __set_PMPxCFG(uint32_t entry_idx, uint8_t pmpxcfg)
{
    rv_csr_t pmpcfgx = 0;
    uint8_t csr_cfg_num = 0;
    uint16_t csr_idx = 0;
    uint16_t cfg_shift = 0;
    if (entry_idx >= __PMP_ENTRY_NUM) return;

#if __RISCV_XLEN == 32
    csr_cfg_num = 4;
    csr_idx = entry_idx >> 2;
#elif __RISCV_XLEN == 64
    csr_cfg_num = 8;
    /* For RV64, pmpcfg0 and pmpcfg2 each hold 8 PMP entries, align by 2 */
    csr_idx = (entry_idx >> 2) & ~1;
#else
    // TODO Add RV128 Handling
    return;
#endif
    /* read specific pmpcfgx register value */
    pmpcfgx = __get_PMPCFGx(csr_idx);
    /*
     * first get specific pmpxcfg's order in one CSR composed of csr_cfg_num pmpxcfgs,
     * then get pmpxcfg's bit position in one CSR by left shift 3(each pmpxcfg size is one byte)
     */
    cfg_shift = (entry_idx & (csr_cfg_num - 1)) << 3;

    pmpcfgx = __RV_INSERT_FIELD(pmpcfgx, 0xFFUL << cfg_shift, pmpxcfg);
    __set_PMPCFGx(csr_idx, pmpcfgx);
}

/**
 * \brief   Get PMPADDRx Register by CSR index
 * \details Return the content of the PMPADDRx Register.
 * \param [in]    csr_idx    PMP region CSR index(0-15)
 * \return        PMPADDRx Register value
 */
__STATIC_INLINE rv_csr_t __get_PMPADDRx(uint32_t csr_idx)
{
    switch (csr_idx) {
        case 0: return __RV_CSR_READ(CSR_PMPADDR0);
        case 1: return __RV_CSR_READ(CSR_PMPADDR1);
        case 2: return __RV_CSR_READ(CSR_PMPADDR2);
        case 3: return __RV_CSR_READ(CSR_PMPADDR3);
        case 4: return __RV_CSR_READ(CSR_PMPADDR4);
        case 5: return __RV_CSR_READ(CSR_PMPADDR5);
        case 6: return __RV_CSR_READ(CSR_PMPADDR6);
        case 7: return __RV_CSR_READ(CSR_PMPADDR7);
        case 8: return __RV_CSR_READ(CSR_PMPADDR8);
        case 9: return __RV_CSR_READ(CSR_PMPADDR9);
        case 10: return __RV_CSR_READ(CSR_PMPADDR10);
        case 11: return __RV_CSR_READ(CSR_PMPADDR11);
        case 12: return __RV_CSR_READ(CSR_PMPADDR12);
        case 13: return __RV_CSR_READ(CSR_PMPADDR13);
        case 14: return __RV_CSR_READ(CSR_PMPADDR14);
        case 15: return __RV_CSR_READ(CSR_PMPADDR15);
        default: return 0;
    }
}

/**
 * \brief   Set PMPADDRx by CSR index
 * \details Write the given value to the PMPADDRx Register.
 * \param [in]    csr_idx  PMP region CSR index(0-15)
 * \param [in]    pmpaddr  PMPADDRx Register value to set
 */
__STATIC_INLINE void __set_PMPADDRx(uint32_t csr_idx, rv_csr_t pmpaddr)
{
    switch (csr_idx) {
        case 0: __RV_CSR_WRITE(CSR_PMPADDR0, pmpaddr); break;
        case 1: __RV_CSR_WRITE(CSR_PMPADDR1, pmpaddr); break;
        case 2: __RV_CSR_WRITE(CSR_PMPADDR2, pmpaddr); break;
        case 3: __RV_CSR_WRITE(CSR_PMPADDR3, pmpaddr); break;
        case 4: __RV_CSR_WRITE(CSR_PMPADDR4, pmpaddr); break;
        case 5: __RV_CSR_WRITE(CSR_PMPADDR5, pmpaddr); break;
        case 6: __RV_CSR_WRITE(CSR_PMPADDR6, pmpaddr); break;
        case 7: __RV_CSR_WRITE(CSR_PMPADDR7, pmpaddr); break;
        case 8: __RV_CSR_WRITE(CSR_PMPADDR8, pmpaddr); break;
        case 9: __RV_CSR_WRITE(CSR_PMPADDR9, pmpaddr); break;
        case 10: __RV_CSR_WRITE(CSR_PMPADDR10, pmpaddr); break;
        case 11: __RV_CSR_WRITE(CSR_PMPADDR11, pmpaddr); break;
        case 12: __RV_CSR_WRITE(CSR_PMPADDR12, pmpaddr); break;
        case 13: __RV_CSR_WRITE(CSR_PMPADDR13, pmpaddr); break;
        case 14: __RV_CSR_WRITE(CSR_PMPADDR14, pmpaddr); break;
        case 15: __RV_CSR_WRITE(CSR_PMPADDR15, pmpaddr); break;
        default: return;
    }
}

/**
 * \brief   Set PMP entry by entry idx
 * \details Write the given value to the PMPxCFG Register and PMPADDRx.
 * \param [in]    entry_idx    PMP entry index(0-15)
 * \param [in]    pmp_cfg      structure of L, X, W, R field of PMP configuration register, memory region base address
 *                and size of memory region as power of 2
 * \remark
 * - If the size of memory region is 2^12(4KB) range, pmp_cfg->order makes 12, and the like.
 * - Suppose the size of memory region is 2^X bytes range, if X >=3, the NA4 mode is not selectable, NAPOT is selected.
 * - TOR of A field in PMP configuration register is not considered here.
 */
__STATIC_INLINE void __set_PMPENTRYx(uint32_t entry_idx, const pmp_config *pmp_cfg)
{
    unsigned int cfg_shift, cfg_csr_idx, addr_csr_idx = 0;
    unsigned long cfgmask, addrmask = 0;
    unsigned long pmpcfg, pmpaddr = 0;
    unsigned long protection, csr_cfg_num = 0;
    /* check parameters */
    if (entry_idx >= __PMP_ENTRY_NUM || pmp_cfg->order > __RISCV_XLEN || pmp_cfg->order < PMP_SHIFT) return;

    /* calculate PMP register and offset */
#if __RISCV_XLEN == 32
    csr_cfg_num = 4;
    cfg_csr_idx = (entry_idx >> 2);
#elif __RISCV_XLEN == 64
    csr_cfg_num = 8;
    cfg_csr_idx = ((entry_idx >> 2)) & ~1;
#else
    // TODO Add RV128 Handling
    return;
#endif
    /*
     * first get specific pmpxcfg's order in one CSR composed of csr_cfg_num pmpxcfgs,
     * then get pmpxcfg's bit position in one CSR by left shift 3, each pmpxcfg size is one byte
     */
    cfg_shift = (entry_idx & (csr_cfg_num - 1)) << 3;
    addr_csr_idx = entry_idx;

    /* encode PMP config */
    protection = (unsigned long)pmp_cfg->protection;
    protection |= (PMP_SHIFT == pmp_cfg->order) ? PMP_A_NA4 : PMP_A_NAPOT;
    cfgmask = ~(0xFFUL << cfg_shift);
    pmpcfg = (__get_PMPCFGx(cfg_csr_idx) & cfgmask);
    pmpcfg |= ((protection << cfg_shift) & ~cfgmask);

    /* encode PMP address */
    if (PMP_SHIFT == pmp_cfg->order) { /* NA4 */
        pmpaddr = (pmp_cfg->base_addr >> PMP_SHIFT);
    } else { /* NAPOT */
        addrmask = (1UL << (pmp_cfg->order - PMP_SHIFT)) - 1;
        pmpaddr = ((pmp_cfg->base_addr >> PMP_SHIFT) & ~addrmask);
        pmpaddr |= (addrmask >> 1);
    }
    /*
     * write csrs, update the address first, in case the entry is locked that
     * we won't be able to modify it after we set the config csr.
     */
    __set_PMPADDRx(addr_csr_idx, pmpaddr);
    __set_PMPCFGx(cfg_csr_idx, pmpcfg);
}

/**
 * \brief   Get PMP entry by entry idx
 * \details Write the given value to the PMPxCFG Register and PMPADDRx.
 * \param [in]     entry_idx     PMP entry index(0-15)
 * \param [out]    pmp_cfg       structure of L, X, W, R, A field of PMP configuration register, memory region base
 *                 address and size of memory region as power of 2
 * \return  -1 failure, else 0 success
 * \remark
 * - If the size of memory region is 2^12(4KB) range, pmp_cfg->order makes 12, and the like.
 * - TOR of A field in PMP configuration register is not considered here.
 */
__STATIC_INLINE int __get_PMPENTRYx(unsigned int entry_idx, pmp_config *pmp_cfg)
{
    unsigned int cfg_shift, cfg_csr_idx, addr_csr_idx = 0;
    unsigned long cfgmask, pmpcfg, prot = 0;
    unsigned long t1, addr, pmpaddr, len = 0;
    uint8_t csr_cfg_num = 0;
    /* check parameters */
    if (entry_idx >= __PMP_ENTRY_NUM || !pmp_cfg) return -1;

    /* calculate PMP register and offset */
#if __RISCV_XLEN == 32
    csr_cfg_num = 4;
    cfg_csr_idx = entry_idx >> 2;
#elif __RISCV_XLEN == 64
    csr_cfg_num = 8;
    cfg_csr_idx = (entry_idx>> 2) & ~1;
#else
// TODO Add RV128 Handling
    return -1;
#endif

    cfg_shift = (entry_idx & (csr_cfg_num - 1)) << 3;
    addr_csr_idx = entry_idx;

    /* decode PMP config */
    cfgmask = (0xFFUL << cfg_shift);
    pmpcfg = (__get_PMPCFGx(cfg_csr_idx) & cfgmask);
    prot = pmpcfg >> cfg_shift;

    /* decode PMP address */
    pmpaddr = __get_PMPADDRx(addr_csr_idx);
    if (PMP_A_NAPOT == (prot & PMP_A)) {
        t1 = __CTZ(~pmpaddr);
        addr = (pmpaddr & ~((1UL << t1) - 1)) << PMP_SHIFT;
        len = (t1 + PMP_SHIFT + 1);
    } else {
        addr = pmpaddr << PMP_SHIFT;
        len = PMP_SHIFT;
    }

    /* return details */
    pmp_cfg->protection = prot;
    pmp_cfg->base_addr = addr;
    pmp_cfg->order = len;

    return 0;
}

/** @} */ /* End of Doxygen Group NMSIS_Core_PMP_Functions */
#endif /* defined(__PMP_PRESENT) && (__PMP_PRESENT == 1) */

#ifdef __cplusplus
}
#endif
#endif /* __CORE_FEATURE_PMP_H__ */
