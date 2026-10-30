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
#ifndef __CORE_FEATURE_PMA_H__
#define __CORE_FEATURE_PMA_H__
/*!
 * @file     core_feature_pma.h
 * @brief    Physical memory attribute feature API header file
 */

#ifdef __cplusplus
 extern "C" {
#endif

#include "core_compatiable.h"

#if defined(__PMA_PRESENT) && (__PMA_PRESENT==1)

/* =====  PMA functions  ===== */
/**
 * \defgroup NMSIS_Core_PMA_Functions         PMA Functions
 * \ingroup  NMSIS_Core
 * \brief    Functions that set/disable/enable different attribute type(Device/Non-Cacheable/Cacheable) memory regions, or get region info.
 * \details
 * Nuclei provide Physical Memory Attribute(PMA) to define the attribute of memory.PMA will affect CPU access memory behavior.
 *
 * PMA are split into three attributes:
 * * Device(abbreviated as 'DEV') Attribute
 * * Non-Cacheable(abbreviated as 'NC') Attribute
 * * Cacheable(abbreviated as 'CA') Attribute
 * And correspondingly, the whole memory region are split into three regions: DEV Region/NC Region/CA Region
 *
 * Hardware provide some software CSR to set the pma by mattri(n)_base/mattri(n)_mask/sattri(n)_base/sattri(n)_mask
 *
 * Hardware defined PMA regions(up to 8 DEV/NC/CA regions) can be disable or enable by CSR mmacro_dev_en/mmacro_noc_en/mmacro_ca_en
 *   @{
 */

#define PMA_REGION_TYPE_SECSHARE      (1UL << 3)    /*!< Set this region shareable between secure world and non-secure world, or else default is invalid */
#define PMA_REGION_TYPE_NC            (1UL << 2)    /*!< Set this region Non-Cacheable, or else default is invalid */
#define PMA_REGION_TYPE_DEV           (1UL << 1)    /*!< Set this region Device, or else default is invalid */
#define PMA_REGION_TYPE_CA            (0)           /*!< Set this region Cacheable, which is default */
#define PMA_REGION_ENA                (1UL << 0)    /*!< Enable this region, then the region type will take effect */
#define PMA_REGION_DIS                (0)           /*!< Disable this region */

typedef struct PMA_CONFIG {
    /**
     * Base physical address, which needs to be 4K byte aligned
     */
    unsigned long region_base;
    /**
     * Region size, which needs to be 4K byte aligned; the \ref region_base should be aligined by \ref region_size
     */
    unsigned long region_size;
    /**
     * Type could be \ref PMA_REGION_TYPE_SECSHARE, \ref PMA_REGION_TYPE_NC, \ref PMA_REGION_TYPE_DEV, \ref PMA_REGION_TYPE_CA
     * \ref PMA_REGION_TYPE_SECSHARE could be combined with one of \ref PMA_REGION_TYPE_NC \ref PMA_REGION_TYPE_DEV \ref PMA_REGION_TYPE_CA
     *  such as \ref PMA_REGION_TYPE_SECSHARE | \ref PMA_REGION_TYPE_NC
     * Reserved for sattri(n)_base
     */
    uint16_t region_type;
    /**
     * Enable or disable the region, could be \ref PMA_REGION_ENA, \ref PMA_REGION_DIS
     */
    uint16_t region_enable;
} pma_config;

/**
 * \brief   Configure one region in machine mode
 * \details  Set the region(0-n) info of base address/region type/region size/enable status
 * \param [in]    entry_idx    Index(0-n) of paired mattri(n)_mask and mattri(n)_base
 * \param [in]    pma_cfg      Region info to configure
 * \return  -1 failure, else 0 success
 * \remarks
 * - The entry_idx(0-n) depends on number of paired mattri(n)_mask and mattri(n)_base, refer to
     Nuclei ISA specifications
 * - Not all the entry_idx(0-n) could set to all the types freely, refer to Nuclei ISA specifications
 * - The mattri(n)_mask must be written first, before mattri(n)_base, which the api takes care of.
 * - The higher bits of mattri(n)_mask should be continuously 1, the remaining lower bits should be all 0
 *   and the number (N) of 0 means the size of this region(2^N bytes)
 * - Region granularity is 4KB, so the low 12-bits of mattri(n)_mask must be 0, which the api takes care of
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 */
__STATIC_INLINE long PMA_SetRegion(unsigned long entry_idx, pma_config *pma_cfg)
{
    // 4KB aligned
    unsigned long size = (pma_cfg->region_size >> 12) << 12;
    unsigned long base_addr = (pma_cfg->region_base >> 12) << 12;

    if ((entry_idx + 1) > __PMA_CSR_NUM) {
        return -1;
    }

    rv_csr_t mask = (unsigned long)(~(size - 1));
    rv_csr_t base = pma_cfg->region_type | base_addr | pma_cfg->region_enable;

    switch (entry_idx) {
        // Bit[MXLEN-1:PA_SIZE] of mattri(n)_mask is reserved 0
        case 0: __RV_CSR_WRITE(CSR_MATTRI0_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI0_BASE, base); break;
        case 1: __RV_CSR_WRITE(CSR_MATTRI1_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI1_BASE, base); break;
        case 2: __RV_CSR_WRITE(CSR_MATTRI2_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI2_BASE, base); break;
        case 3: __RV_CSR_WRITE(CSR_MATTRI3_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI3_BASE, base); break;
        case 4: __RV_CSR_WRITE(CSR_MATTRI4_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI4_BASE, base); break;
        case 5: __RV_CSR_WRITE(CSR_MATTRI5_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI5_BASE, base); break;
        case 6: __RV_CSR_WRITE(CSR_MATTRI6_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI6_BASE, base); break;
        case 7: __RV_CSR_WRITE(CSR_MATTRI7_MASK, mask); __RV_CSR_WRITE(CSR_MATTRI7_BASE, base); break;
        default: return -1;
    }

    return 0;
}

/**
 * \brief    Get the region info in machine mode
 * \details  Read the region(0-n) info of base address/region type/region size/enable status
 * \param [in]    entry_idx    Index(0-n) of paired mattri(n)_mask and mattri(n)_base
 * \param [out]   pma_cfg      Region info read
 * \return  0 if success, else -1
 * \remarks
 * - entry_idx(0-n) depends on number of paired mattri(n)_mask and mattri(n)_base, refer to
     Nuclei ISA specifications
 * - Not all the entry_idx(0-n) could set to all the types freely, refer to Nuclei ISA specifications
 */
__STATIC_INLINE long PMA_GetRegion(unsigned long entry_idx, pma_config *pma_cfg)
{
    rv_csr_t mask, base;
    uint32_t mpasize = *(uint32_t *)__IINFO_MPASIZE_ADDR;

    if ((entry_idx + 1) > __PMA_CSR_NUM) {
        return -1;
    }

    switch (entry_idx) {
        case 0: mask = __RV_CSR_READ(CSR_MATTRI0_MASK); base = __RV_CSR_READ(CSR_MATTRI0_BASE); break;
        case 1: mask = __RV_CSR_READ(CSR_MATTRI1_MASK); base = __RV_CSR_READ(CSR_MATTRI1_BASE); break;
        case 2: mask = __RV_CSR_READ(CSR_MATTRI2_MASK); base = __RV_CSR_READ(CSR_MATTRI2_BASE); break;
        case 3: mask = __RV_CSR_READ(CSR_MATTRI3_MASK); base = __RV_CSR_READ(CSR_MATTRI3_BASE); break;
        case 4: mask = __RV_CSR_READ(CSR_MATTRI4_MASK); base = __RV_CSR_READ(CSR_MATTRI4_BASE); break;
        case 5: mask = __RV_CSR_READ(CSR_MATTRI5_MASK); base = __RV_CSR_READ(CSR_MATTRI5_BASE); break;
        case 6: mask = __RV_CSR_READ(CSR_MATTRI6_MASK); base = __RV_CSR_READ(CSR_MATTRI6_BASE); break;
        case 7: mask = __RV_CSR_READ(CSR_MATTRI7_MASK); base = __RV_CSR_READ(CSR_MATTRI7_BASE); break;
        default: return -1;
    }

    pma_cfg->region_type = (unsigned long)(base & 0x0E);
    pma_cfg->region_base = (unsigned long)((base >> 12) << 12);
    pma_cfg->region_size = (unsigned long)(1UL << (mask == 0 ? mpasize : __CTZ(mask)));
    pma_cfg->region_enable = (uint16_t)(base & 0x01);

    return 0;
}

/**
 * \brief    Configure one region for Secure S-Mode world to share with Non-Secure S-Mode world
 * \details  Set the region(0-7) info of base address/region size/enable status
 * \param [in]    entry_idx    Index(0-7) of paired sattri(n)_mask and sattri(n)_base
 * \param [in]    pma_cfg      Region info to configure
 * \return  0 if success, else -1
 * \remarks
 * - sattri(n)_mask must be written first, before sattri(n)_base, which the api takes care of
 * - The higher bits of sattri(n)_mask should be continuously 1, the remaining lower bits should be all 0
 *   and the number (N) of 0 means the size of this region(2^N bytes)
 * - Region granularity is 4KB, so the low 12-bits of sattri(n)_mask must be 0, which the api takes care of
 * - Unlike mattri(n)_base, there's no DEV Region/NC Region/CA Region type
 */
__STATIC_INLINE long PMA_SetRegion_S(unsigned long entry_idx, pma_config *pma_cfg)
{
    // 4KB aligned
    unsigned long size = (pma_cfg->region_size >> 12) << 12;
    unsigned long base_addr = (pma_cfg->region_base >> 12) << 12;

    if ((entry_idx + 1) > __PMA_SEC_CSR_NUM) {
        return -1;
    }

    rv_csr_t mask = (unsigned long)(~(size - 1));
    rv_csr_t base = base_addr | pma_cfg->region_enable;

    switch (entry_idx) {
        // Bit[MXLEN-1:PA_SIZE] of sattri(n)_mask is reserved 0
        case 0: __RV_CSR_WRITE(CSR_SATTRI0_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI0_BASE, base); break;
        case 1: __RV_CSR_WRITE(CSR_SATTRI1_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI1_BASE, base); break;
        case 2: __RV_CSR_WRITE(CSR_SATTRI2_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI2_BASE, base); break;
        case 3: __RV_CSR_WRITE(CSR_SATTRI3_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI3_BASE, base); break;
        case 4: __RV_CSR_WRITE(CSR_SATTRI4_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI4_BASE, base); break;
        case 5: __RV_CSR_WRITE(CSR_SATTRI5_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI5_BASE, base); break;
        case 6: __RV_CSR_WRITE(CSR_SATTRI6_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI6_BASE, base); break;
        case 7: __RV_CSR_WRITE(CSR_SATTRI7_MASK, mask); __RV_CSR_WRITE(CSR_SATTRI7_BASE, base); break;
        default: return -1;
    }

    return 0;
}

/**
 * \brief    Get the region info of Secure S-Mode world sharing with Non-Secure S-Mode world
 * \details  Read the region(0-7) info of base address/region size/enable status
 * \param [in]    entry_idx    Index(0-7) of paired sattri(n)_mask and sattri(n)_base
 * \param [out]   pma_cfg      Region info read
 * \return  0 if success, else -1
 * \remark
 * - Unlike mattri(n)_base, there's no DEV Region/NC Region/CA Region type
 */
__STATIC_INLINE long PMA_GetRegion_S(unsigned long entry_idx, pma_config *pma_cfg)
{
    rv_csr_t mask, base;
    uint32_t mpasize = *(uint32_t *)__IINFO_MPASIZE_ADDR;

    if ((entry_idx + 1) > __PMA_SEC_CSR_NUM) {
        return -1;
    }

    switch (entry_idx) {
        case 0: mask = __RV_CSR_READ(CSR_SATTRI0_MASK); base = __RV_CSR_READ(CSR_SATTRI0_BASE); break;
        case 1: mask = __RV_CSR_READ(CSR_SATTRI1_MASK); base = __RV_CSR_READ(CSR_SATTRI1_BASE); break;
        case 2: mask = __RV_CSR_READ(CSR_SATTRI2_MASK); base = __RV_CSR_READ(CSR_SATTRI2_BASE); break;
        case 3: mask = __RV_CSR_READ(CSR_SATTRI3_MASK); base = __RV_CSR_READ(CSR_SATTRI3_BASE); break;
        case 4: mask = __RV_CSR_READ(CSR_SATTRI4_MASK); base = __RV_CSR_READ(CSR_SATTRI4_BASE); break;
        case 5: mask = __RV_CSR_READ(CSR_SATTRI5_MASK); base = __RV_CSR_READ(CSR_SATTRI5_BASE); break;
        case 6: mask = __RV_CSR_READ(CSR_SATTRI6_MASK); base = __RV_CSR_READ(CSR_SATTRI6_BASE); break;
        case 7: mask = __RV_CSR_READ(CSR_SATTRI7_MASK); base = __RV_CSR_READ(CSR_SATTRI7_BASE); break;
        default: return -1;
    }

    pma_cfg->region_base = (unsigned long)((base >> 12) << 12);
    pma_cfg->region_size = (unsigned long)(1UL << (mask == 0 ? mpasize : __CTZ(mask)));
    pma_cfg->region_enable = (uint16_t)(base & 0x01);

    return 0;
}

#if defined(__PMA_MACRO_PRESENT) && (__PMA_MACRO_PRESENT == 1)
/**
 * \brief  Enable hardware defined Device regions
 * \details Enable Device region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_DisableHwDevRegion
*/
__STATIC_FORCEINLINE void PMA_EnableHwDevRegion(unsigned long entry_idx)
{
    __RV_CSR_SET(CSR_MMACRO_DEV_EN, 1UL << entry_idx);
}

/**
 * \brief  Disable hardware defined Device regions
 * \details Disable Device region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_EnableHwDevRegion
*/
__STATIC_FORCEINLINE void PMA_DisableHwDevRegion(unsigned long entry_idx)
{
    __RV_CSR_CLEAR(CSR_MMACRO_DEV_EN, 1UL << entry_idx);
}

/**
 * \brief  Enable hardware defined Non-Cacheable regions
 * \details Enable Non-Cacheable region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_DisableHwNCRegion
*/
__STATIC_FORCEINLINE void PMA_EnableHwNCRegion(unsigned long entry_idx)
{
    __RV_CSR_SET(CSR_MMACRO_NOC_EN, 1UL << entry_idx);
}

/**
 * \brief  Disable hardware defined Non-Cacheable regions
 * \details Disable Non-Cacheable region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_EnableHwNCRegion
*/
__STATIC_FORCEINLINE void PMA_DisableHwNCRegion(unsigned long entry_idx)
{
    __RV_CSR_CLEAR(CSR_MMACRO_NOC_EN, 1UL << entry_idx);
}

/**
 * \brief  Enable hardware defined Cacheable regions
 * \details Enable Cacheable region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_DisableHwCARegion
*/
__STATIC_FORCEINLINE void PMA_EnableHwCARegion(unsigned long entry_idx)
{
    __RV_CSR_SET(CSR_MMACRO_CA_EN, 1UL << entry_idx);
}

/**
 * \brief  Disable hardware defined Cacheable regions
 * \details Disable Cacheable region by corresponding index
 * \param [in]    entry_idx    Index(0-7)
 * \remarks
 * - This function can be called in M-Mode only.
 * - When there is no entry_idx, this field is tied to 0
 * - For each region entry's address/size/attribute detail refers to RTL Configuration Stage
 * - The regions can be overlapped as the prority: Non-Cacheable > Cacheable > Device, but especially be careful not to
 *   overlap software's instruction/data sections by Device, or overlap Device(like uart) memory by Cacheable
 * \sa
 * - \ref PMA_EnableHwCARegion
*/
__STATIC_FORCEINLINE void PMA_DisableHwCARegion(unsigned long entry_idx)
{
    __RV_CSR_CLEAR(CSR_MMACRO_CA_EN, 1UL << entry_idx);
}
#endif /* defined(__PMA_MACRO_PRESENT) && (__PMA_MACRO_PRESENT == 1) */
/** @} */ /* End of Doxygen Group NMSIS_Core_PMA_Functions */
#endif /* defined(__PMA_PRESENT) && (__PMA_PRESENT==1) */

#ifdef __cplusplus
}
#endif
#endif /* __CORE_FEATURE_PMA_H__ */
