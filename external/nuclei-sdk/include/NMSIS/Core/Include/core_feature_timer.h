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
#ifndef __CORE_FEATURE_TIMER_H__
#define __CORE_FEATURE_TIMER_H__
/*!
 * @file     core_feature_timer.h
 * @brief    System Timer feature API header file for Nuclei N/NX Core
 */
/*
 * System Timer Feature Configuration Macro:
 * 1. __SYSTIMER_PRESENT: Must, Define whether Private System Timer is present or not.
 *   * 0: Not present
 *   * 1: Present
 * 2. __SYSTIMER_BASEADDR: Must, Define the base address of the System Timer.
 * 3. __SYSTIMER_HARTID:  Optional, Define the system timer hart index of the cpu, important for case when cpu hartid and cpu hart index are different, only set it if your cpu is single core.
 */
#ifdef __cplusplus
extern "C" {
#endif

#include "core_feature_base.h"

#if defined(__SYSTIMER_PRESENT) && (__SYSTIMER_PRESENT == 1)
/**
 * \defgroup NMSIS_Core_SysTimer_Registers     Register Define and Type Definitions Of System Timer
 * \ingroup NMSIS_Core_Registers
 * \brief   Type definitions and defines for system timer registers.
 *
 * @{
 */
/**
 * \brief  Structure type to access the System Timer (SysTimer).
 * \details
 * Structure definition to access the system timer(SysTimer).
 * \remarks
 * - MSFTRST register is introduced in Nuclei N Core version 1.3(\ref __NUCLEI_N_REV >= 0x0103)
 * - MSTOP register is renamed to MTIMECTL register in Nuclei N Core version 1.4(\ref __NUCLEI_N_REV >= 0x0104)
 * - CMPCLREN and CLKSRC bit in MTIMECTL register is introduced in Nuclei N Core version 1.4(\ref __NUCLEI_N_REV >= 0x0104)
 */
typedef struct {
    __IOM uint64_t MTIMER;                  /*!< Offset: 0x000 (R/W)  System Timer current value 64bits Register */
    __IOM uint64_t MTIMERCMP;               /*!< Offset: 0x008 (R/W)  System Timer compare Value 64bits Register */
    __IOM uint32_t RESERVED0[0x3F7];        /*!< Offset: 0x010 - 0xFE8 Reserved */
    __IOM uint32_t MTIME_SRW_CTRL;          /*!< Offset: 0xFEC (R/W)  Control S-mode can access this timer or not. */
    __IOM uint32_t MSFTRST;                 /*!< Offset: 0xFF0 (R/W)  System Timer Software Core Reset Register */
    __IOM uint32_t SSIP;                    /*!< Offset: 0xFF4 (R/W)  S-Mode System Timer SW interrupt Register */
    __IOM uint32_t MTIMECTL;                /*!< Offset: 0xFF8 (R/W)  System Timer Control Register, previously MSTOP register */
    __IOM uint32_t MSIP;                    /*!< Offset: 0xFFC (R/W)  M-Mode System Timer SW interrupt Register */
} SysTimer_Type;

/* Timer Control / Status Register Definitions */
#define SysTimer_MTIMECTL_TIMESTOP_Pos      0U                                          /*!< SysTick Timer MTIMECTL: TIMESTOP bit Position */
#define SysTimer_MTIMECTL_TIMESTOP_Msk      (1UL << SysTimer_MTIMECTL_TIMESTOP_Pos)     /*!< SysTick Timer MTIMECTL: TIMESTOP Mask */
#define SysTimer_MTIMECTL_CMPCLREN_Pos      1U                                          /*!< SysTick Timer MTIMECTL: CMPCLREN bit Position */
#define SysTimer_MTIMECTL_CMPCLREN_Msk      (1UL << SysTimer_MTIMECTL_CMPCLREN_Pos)     /*!< SysTick Timer MTIMECTL: CMPCLREN Mask */
#define SysTimer_MTIMECTL_CLKSRC_Pos        2U                                          /*!< SysTick Timer MTIMECTL: CLKSRC bit Position */
#define SysTimer_MTIMECTL_CLKSRC_Msk        (1UL << SysTimer_MTIMECTL_CLKSRC_Pos)       /*!< SysTick Timer MTIMECTL: CLKSRC Mask */
#define SysTimer_MTIMECTL_HDBG_Pos          4U                                          /*!< SysTick Timer MTIMECTL: HDBG bit Position */
#define SysTimer_MTIMECTL_HDBG_Msk          (1UL << SysTimer_MTIMECTL_HDBG_Pos)         /*!< SysTick Timer MTIMECTL: HDBG Mask */


#define SysTimer_MSIP_MSIP_Pos              0U                                          /*!< SysTick Timer MSIP: MSIP bit Position */
#define SysTimer_MSIP_MSIP_Msk              (1UL << SysTimer_MSIP_MSIP_Pos)             /*!< SysTick Timer MSIP: MSIP Mask */

#define SysTimer_SSIP_SSIP_Pos              0U                                          /*!< SysTick Timer SSIP: SSIP bit Position */
#define SysTimer_SSIP_SSIP_Msk              (1UL << SysTimer_SSIP_SSIP_Pos)             /*!< SysTick Timer SSIP: SSIP Mask */

#define SysTimer_MTIMER_Msk                 (0xFFFFFFFFFFFFFFFFULL)                     /*!< SysTick Timer MTIMER value Mask */
#define SysTimer_MTIMERCMP_Msk              (0xFFFFFFFFFFFFFFFFULL)                     /*!< SysTick Timer MTIMERCMP value Mask */
#define SysTimer_MTIMECTL_Msk               (0xFFFFFFFFUL)                              /*!< SysTick Timer MTIMECTL/MSTOP value Mask */
#define SysTimer_MSIP_Msk                   (0xFFFFFFFFUL)                              /*!< SysTick Timer MSIP   value Mask */
#define SysTimer_MSFTRST_Msk                (0xFFFFFFFFUL)                              /*!< SysTick Timer MSFTRST value Mask */

#define SysTimer_MSFRST_KEY                 (0x80000A5FUL)                              /*!< SysTick Timer Software Reset Request Key */

#define SysTimer_CLINT_MSIP_OFS             (0x1000UL)                                  /*!< Machine Mode Software interrupt register offset of clint mode in SysTick Timer */
#define SysTimer_CLINT_MTIMECMP_OFS         (0x5000UL)                                  /*!< MTIMECMP register offset of clint mode in SysTick Timer */
#define SysTimer_CLINT_MTIME_OFS            (0xCFF8UL)                                  /*!< MTIME register offset of clint mode in SysTick Timer */
#define SysTimer_CLINT_SSIP_OFS             (0xD000UL)                                  /*!< Supervisor Mode Software interrupt register offset of clint mode in SysTick Timer */

#ifndef __SYSTIMER_BASEADDR
/* Base address of SYSTIMER(__SYSTIMER_BASEADDR) should be defined in <Device.h> */
#error "__SYSTIMER_BASEADDR is not defined, please check!"
#endif
/* System Timer Memory mapping of Device  */
#define SysTimer_BASE                       __SYSTIMER_BASEADDR                         /*!< SysTick Base Address */
#define SysTimer                            ((SysTimer_Type *) SysTimer_BASE)           /*!< SysTick configuration struct */

/* System Timer Clint register base */
#define SysTimer_CLINT_MSIP_BASE(hartid)        (unsigned long)((SysTimer_BASE) + (SysTimer_CLINT_MSIP_OFS) + ((hartid) << 2))
#define SysTimer_CLINT_MTIMECMP_BASE(hartid)    (unsigned long)((SysTimer_BASE) + (SysTimer_CLINT_MTIMECMP_OFS) + ((hartid) << 3))
#define SysTimer_CLINT_MTIME_BASE               (unsigned long)((SysTimer_BASE) + (SysTimer_CLINT_MTIME_OFS))
#define SysTimer_CLINT_SSIP_BASE(hartid)        (unsigned long)((SysTimer_BASE) + (SysTimer_CLINT_SSIP_OFS) + ((hartid) << 2))

/** @} */ /* end of group NMSIS_Core_SysTimer_Registers */

/* ##################################    SysTimer function  ############################################ */
/**
 * \defgroup NMSIS_Core_SysTimer SysTimer Functions
 * \brief    Functions that configure the Core System Timer.
 * @{
 */

/**
 * SysTimer_GetHartID() is used to get timer hartid which might not be the same as cpu hart id,
 * for example, cpu hartid may be 1, but timer hartid may be 0, then timer hartid offset is 1.
 * If defined __SYSTIMER_HARTID, it will use __SYSTIMER_HARTID as timer hartid,
 * otherwise, it will use __get_hart_index().
 * The cpu hartid is get by using __get_hart_id function
 */
#ifndef __SYSTIMER_HARTID
#define SysTimer_GetHartID()                    (__get_hart_index())
#else
#define SysTimer_GetHartID()                    (__SYSTIMER_HARTID)
#endif

#if defined(__SSTC_PRESENT) && (__SSTC_PRESENT == 1)
#ifndef __SYSTIMER_HARTID
#define SysTimer_GetHartID_S()                  (__get_hart_index_s())
#else
#define SysTimer_GetHartID_S()                  (__SYSTIMER_HARTID)
#endif
#endif

/**
 * \brief  Set system timer load value
 * \details
 * This function set the system timer load value in MTIMER register.
 * \param [in]  value   value to set system timer MTIMER register.
 * \remarks
 * - Load value is 64bits wide.
 * - \ref SysTimer_GetLoadValue
 */
__STATIC_INLINE void SysTimer_SetLoadValue(uint64_t value)
{
#if __RISCV_XLEN == 32
    uint8_t *addr;
    addr = (uint8_t *)(&(SysTimer->MTIMER));
    __SW(addr, 0);      // prevent carry
    __SW(addr + 4, (uint32_t)(value >> 32));
    __SW(addr, (uint32_t)(value));
#else
    SysTimer->MTIMER = value;
#endif
}

/**
 * \brief  Get system timer load value
 * \details
 * This function get the system timer current value in MTIMER register.
 * \return  current value(64bit) of system timer MTIMER register.
 * \remarks
 * - Load value is 64bits wide.
 * - \ref SysTimer_SetLoadValue
 */
__STATIC_INLINE uint64_t SysTimer_GetLoadValue(void)
{
#if __RISCV_XLEN == 32
    volatile uint32_t high0, low, high;
    uint64_t full;
    uint8_t *addr;

    addr = (uint8_t *)(&(SysTimer->MTIMER));

    high0 = __LW(addr + 4);
    low = __LW(addr);
    high = __LW(addr + 4);
    if (high0 != high) {
        low = __LW(addr);
    }
    full = (((uint64_t)high) << 32) | low;
    return full;
#else
    return SysTimer->MTIMER;
#endif
}

/**
 * \brief  Set system timer compare value by hartid
 * \details
 * This function set the system Timer compare value in MTIMERCMP register.
 * \param [in]  value   compare value to set system timer MTIMERCMP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - Compare value is 64bits wide.
 * - If compare value is larger than current value timer interrupt generate.
 * - Modify the load value or compare value less to clear the interrupt.
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * - \ref SysTimer_GetHartCompareValue
 */
__STATIC_INLINE void SysTimer_SetHartCompareValue(uint64_t value, unsigned long hartid)
{
    if (hartid == 0) {
#if __RISCV_XLEN == 32
        uint8_t *addr;
        addr = (uint8_t *)(&(SysTimer->MTIMERCMP));
        __SW(addr, -1U);      // prevent load > timecmp
        __SW(addr + 4, (uint32_t)(value >> 32));
        __SW(addr, (uint32_t)(value));
#else
        SysTimer->MTIMERCMP = value;
#endif
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MTIMECMP_BASE(hartid));
#if __RISCV_XLEN == 32
        __SW(addr, -1U);      // prevent load > timecmp
        __SW(addr + 4, (uint32_t)(value >> 32));
        __SW(addr, (uint32_t)value);
#else
        __SD(addr, value);
#endif
    }
}

/**
 * \brief  Set system timer compare value in machine mode
 * \details
 * This function set the system Timer compare value in MTIMERCMP register.
 * \param [in]  value   compare value to set system timer MTIMERCMP register.
 * \remarks
 * - Compare value is 64bits wide.
 * - If compare value is larger than current value timer interrupt generate.
 * - Modify the load value or compare value less to clear the interrupt.
 * - __get_hart_id function can only be accessed in machine mode, or else exception will occur.
 * - \ref SysTimer_GetCompareValue
 */
__STATIC_FORCEINLINE void SysTimer_SetCompareValue(uint64_t value)
{
    unsigned long hartid = SysTimer_GetHartID();
    SysTimer_SetHartCompareValue(value, hartid);
}

/**
 * \brief  Get system timer compare value by hartid
 * \details
 * This function get the system timer compare value in MTIMERCMP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \return  compare value of system timer MTIMERCMP register.
 * \remarks
 * - Compare value is 64bits wide.
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * - \ref SysTimer_SetHartCompareValue
 */
__STATIC_INLINE uint64_t SysTimer_GetHartCompareValue(unsigned long hartid)
{
    if (hartid == 0) {
        return SysTimer->MTIMERCMP;
    } else {
        uint64_t full;
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MTIMECMP_BASE(hartid));
#if __RISCV_XLEN == 32
        // MTIMECMP didn't increase
        uint32_t high, low;

        high = __LW(addr + 4);
        low = __LW(addr);
        full = (((uint64_t)high) << 32) | low;
#else
        full = __LD(addr);
#endif
        return full;
    }
}

/**
 * \brief  Get system timer compare value in machine mode
 * \details
 * This function get the system timer compare value in MTIMERCMP register.
 * \return  compare value of system timer MTIMERCMP register.
 * \remarks
 * - Compare value is 64bits wide.
 * - \ref SysTimer_SetCompareValue
 */
__STATIC_FORCEINLINE uint64_t SysTimer_GetCompareValue(void)
{
    unsigned long hartid = SysTimer_GetHartID();
    return SysTimer_GetHartCompareValue(hartid);
}

/**
 * \brief  Enable system timer counter running
 * \details
 * Enable system timer counter running by clear
 * TIMESTOP bit in MTIMECTL register.
 */
__STATIC_FORCEINLINE void SysTimer_Start(void)
{
    SysTimer->MTIMECTL &= ~(SysTimer_MTIMECTL_TIMESTOP_Msk);
}

/**
 * \brief  Stop system timer counter running
 * \details
 * Stop system timer counter running by set
 * TIMESTOP bit in MTIMECTL register.
 */
__STATIC_FORCEINLINE void SysTimer_Stop(void)
{
    SysTimer->MTIMECTL |= SysTimer_MTIMECTL_TIMESTOP_Msk;
}

/**
 * \brief  Set system timer control value
 * \details
 * This function set the system timer MTIMECTL register value.
 * \param [in]  mctl    value to set MTIMECTL register
 * \remarks
 * - Bit TIMESTOP is used to start and stop timer.
 *   Clear TIMESTOP bit to 0 to start timer, otherwise to stop timer.
 * - Bit CMPCLREN is used to enable auto MTIMER clear to zero when MTIMER >= MTIMERCMP.
 *   Clear CMPCLREN bit to 0 to stop auto clear MTIMER feature, otherwise to enable it.
 * - Bit CLKSRC is used to select timer clock source.
 *   Clear CLKSRC bit to 0 to use *mtime_toggle_a*, otherwise use *core_clk_aon*
 * - \ref SysTimer_GetControlValue
 */
__STATIC_FORCEINLINE void SysTimer_SetControlValue(uint32_t mctl)
{
    SysTimer->MTIMECTL = (mctl & SysTimer_MTIMECTL_Msk);
}

/**
 * \brief  Get system timer control value
 * \details
 * This function get the system timer MTIMECTL register value.
 * \return  MTIMECTL register value
 * \remarks
 * - \ref SysTimer_SetControlValue
 */
__STATIC_FORCEINLINE uint32_t SysTimer_GetControlValue(void)
{
    return (SysTimer->MTIMECTL & SysTimer_MTIMECTL_Msk);
}

/**
 * \brief  Trigger or set software interrupt via system timer by hartid
 * \details
 * This function set the system timer MSIP bit in MSIP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - Set system timer MSIP bit and generate a machine mode software interrupt.
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suite S-mode particularly when MTIME_SRW_CTRL.SRW equal 0.
 * - \ref SysTimer_ClearHartSWIRQ
 * - \ref SysTimer_GetHartMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetHartSWIRQ(unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->MSIP |= SysTimer_MSIP_MSIP_Msk;
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
        __SW(addr, SysTimer_MSIP_MSIP_Msk);
    }
}

/**
 * \brief  Trigger or set software interrupt via system timer in machine mode
 * \details
 * This function set the system timer MSIP bit in MSIP register.
 * \remarks
 * - Set system timer MSIP bit and generate a SW interrupt.
 * - \ref SysTimer_ClearSWIRQ
 * - \ref SysTimer_GetMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetSWIRQ(void)
{
    unsigned long hartid = SysTimer_GetHartID();
    SysTimer_SetHartSWIRQ(hartid);
}

/**
 * \brief  Clear system timer software interrupt pending request by hartid
 * \details
 * This function clear the system timer MSIP bit in MSIP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - Clear system timer MSIP bit in MSIP register to clear the software interrupt pending.
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * - \ref SysTimer_SetHartSWIRQ
 * - \ref SysTimer_GetHartMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_ClearHartSWIRQ(unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->MSIP &= ~SysTimer_MSIP_MSIP_Msk;
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
        __SW(addr, 0);
    }
}

/**
 * \brief  Clear system timer software interrupt pending request in machine mode
 * \details
 * This function clear the system timer MSIP bit in MSIP register.
 * \remarks
 * - Clear system timer MSIP bit in MSIP register to clear the software interrupt pending.
 * - \ref SysTimer_SetSWIRQ
 * - \ref SysTimer_GetMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_ClearSWIRQ(void)
{
    unsigned long hartid = SysTimer_GetHartID();
    SysTimer_ClearHartSWIRQ(hartid);
}

/**
 * \brief  Get system timer MSIP register value by hartid
 * \details
 * This function get the system timer MSIP register value.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \return    Value of Timer MSIP register.
 * \remarks
 * - Bit0 is SW interrupt flag.
 *   Bit0 is 1 then SW interrupt set. Bit0 is 0 then SW interrupt clear.
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * - \ref SysTimer_SetHartSWIRQ
 * - \ref SysTimer_ClearHartSWIRQ
 * - \ref SysTimer_SetHartMsipValue
 */
__STATIC_FORCEINLINE uint32_t SysTimer_GetHartMsipValue(unsigned long hartid)
{
    if (hartid == 0) {
        return (uint32_t)(SysTimer->MSIP);
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
        return __LW(addr);
    }
}

/**
 * \brief  Get system timer MSIP register value in machine mode
 * \details
 * This function get the system timer MSIP register value.
 * \return    Value of Timer MSIP register.
 * \remarks
 * - Bit0 is SW interrupt flag.
 *   Bit0 is 1 then SW interrupt set. Bit0 is 0 then SW interrupt clear.
 * - \ref SysTimer_SetSWIRQ
 * - \ref SysTimer_ClearSWIRQ
 * - \ref SysTimer_SetMsipValue
 */
__STATIC_FORCEINLINE uint32_t SysTimer_GetMsipValue(void)
{
    unsigned long hartid = SysTimer_GetHartID();
    return SysTimer_GetHartMsipValue(hartid);
}

/**
 * \brief  Set system timer MSIP register value by hartid
 * \details
 * This function set the system timer MSIP register value.
 * \param [in]  msip   value to set MSIP register
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - In S-mode, hartid can't be get using __get_hart_id function, so this api suits S-mode particularly.
 * - \ref SysTimer_GetHartMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetHartMsipValue(uint32_t msip, unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->MSIP = (msip);
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
        __SW(addr, msip);
    }
}

/**
 * \brief  Set system timer MSIP register value in machine mode
 * \details
 * This function set the system timer MSIP register value.
 * \param [in]  msip   value to set MSIP register
 * - \ref SysTimer_GetMsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetMsipValue(uint32_t msip)
{
    unsigned long hartid = SysTimer_GetHartID();
    SysTimer_SetHartMsipValue(msip, hartid);
}

#if defined(__SSTC_PRESENT) && (__SSTC_PRESENT == 1)
/**
 * \brief  Set system timer smode compare value
 * \details
 * This function set the system timer smode compare value in STIMECMP and STIMECMPH CSR register.
 * \param [in]  value   compare value to set system timer smode compare register.
 * \remarks
 * - smode timer compare regiser required the SSTC extension
 * - smode timer compare value located in stimecmp/stimecmph for rv32 and stimecmp for rv64.
 * - If compare value is larger than current value smode timer interrupt generate.
 * - Modify the load value or compare value less to clear the interrupt.
 * - \ref SysTimer_GetCompareValue_S
 */
__STATIC_INLINE void SysTimer_SetCompareValue_S(uint64_t value)
{
#if __RISCV_XLEN == 32
    __RV_CSR_WRITE(CSR_STIMECMP, -1U);      // prevent load > timecmp
    __RV_CSR_WRITE(CSR_STIMECMPH, (uint32_t)(value >> 32));
    __RV_CSR_WRITE(CSR_STIMECMP, (uint32_t)value);
#else
    __RV_CSR_WRITE(CSR_STIMECMP, value);
#endif
}

/**
 * \brief  Get system timer smode compare value
 * \details
 * This function get the system timer smode compare value in STIMERCMP and STIMECMPH CSR register.
 * \return  compare value of system timer smode compare csr register in 64bit.
 * \remarks
 * - Compare value is 64bits wide.
 * - \ref SysTimer_SetCompareValue_S
 */
__STATIC_INLINE uint64_t SysTimer_GetCompareValue_S(void)
{
    uint64_t full;
#if __RISCV_XLEN == 32
    uint32_t high, low;

    high = __RV_CSR_READ(CSR_STIMECMPH);
    low = __RV_CSR_READ(CSR_STIMECMP);
    full = (((uint64_t)high) << 32) | low;
#else
    full = __RV_CSR_READ(CSR_STIMECMP);
#endif
    return full;
}

/**
 * \brief  Trigger or set supervisor mode software interrupt via system timer by hartid
 * \details
 * This function set the system timer SSIP bit in SSIP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - Set system timer SSIP bit and generate a supervisor mode software interrupt.
 * - \ref SysTimer_ClearHartSWIRQ_S
 * - \ref SysTimer_GetHartSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetHartSWIRQ_S(unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->SSIP |= SysTimer_SSIP_SSIP_Msk;
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
        __SW(addr, SysTimer_SSIP_SSIP_Msk);
    }
}

/**
 * \brief  Trigger or set supervisor software interrupt via system timer
 * \details
 * This function set the system timer SSIP bit in SSIP register.
 * \remarks
 * - Set system timer SSIP bit and generate a supervisor mode SW interrupt.
 * - \ref SysTimer_ClearSWIRQ_S
 * - \ref SysTimer_GetSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetSWIRQ_S(void)
{
    unsigned long hartid = SysTimer_GetHartID_S();
    SysTimer_SetHartSWIRQ_S(hartid);
}

/**
 * \brief  Clear system timer supervisor mode software interrupt pending request by hartid
 * \details
 * This function clear the system timer SSIP bit in SSIP register.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - Clear system timer SSIP bit in SSIP register to clear the supervisor mode software interrupt pending.
 * - \ref SysTimer_SetHartSWIRQ_S
 * - \ref SysTimer_GetHartSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_ClearHartSWIRQ_S(unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->SSIP &= ~SysTimer_SSIP_SSIP_Msk;
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
        __SW(addr, 0);
    }
}

/**
 * \brief  Clear system timer supervisor mode software interrupt pending request
 * \details
 * This function clear the system timer SSIP bit in SSIP register.
 * \remarks
 * - Clear system timer SSIP bit in SSIP register to clear the supervisor mode software interrupt pending.
 * - \ref SysTimer_SetSWIRQ_S
 * - \ref SysTimer_GetSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_ClearSWIRQ_S(void)
{
    unsigned long hartid = SysTimer_GetHartID_S();
    SysTimer_ClearHartSWIRQ_S(hartid);
}

/**
 * \brief  Get system timer SSIP register value by hartid
 * \details
 * This function get the system timer SSIP register value.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \return    Value of Timer SSIP register.
 * \remarks
 * - Bit0 is SW interrupt flag.
 *   Bit0 is 1 then SW interrupt set. Bit0 is 0 then SW interrupt clear.
 * - \ref SysTimer_SetHartSWIRQ_S
 * - \ref SysTimer_ClearHartSWIRQ_S
 * - \ref SysTimer_SetHartSsipValue
 */
__STATIC_FORCEINLINE uint32_t SysTimer_GetHartSsipValue(unsigned long hartid)
{
    if (hartid == 0) {
        return (uint32_t)(SysTimer->SSIP);
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
        return __LW(addr);
    }
}

/**
 * \brief  Get system timer SSIP register value
 * \details
 * This function get the system timer MSIP register value.
 * \return    Value of Timer MSIP register.
 * \remarks
 * - Bit0 is SW interrupt flag.
 *   Bit0 is 1 then SW interrupt set. Bit0 is 0 then SW interrupt clear.
 * - \ref SysTimer_SetSWIRQ_S
 * - \ref SysTimer_ClearSWIRQ_S
 * - \ref SysTimer_SetSsipValue
 */
__STATIC_FORCEINLINE uint32_t SysTimer_GetSsipValue(void)
{
    unsigned long hartid = SysTimer_GetHartID_S();
    return SysTimer_GetHartSsipValue(hartid);
}

/**
 * \brief  Set system timer SSIP register value by hartid
 * \details
 * This function set the system timer SSIP register value.
 * \param [in]  msip   value to set SSIP register
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \remarks
 * - \ref SysTimer_GetHartSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetHartSsipValue(uint32_t ssip, unsigned long hartid)
{
    if (hartid == 0) {
        SysTimer->SSIP = (ssip);
    } else {
        uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
        __SW(addr, ssip);
    }
}

/**
 * \brief  Set system timer SSIP register value
 * \details
 * This function set the system timer SSIP register value.
 * \param [in]  msip   value to set SSIP register
 * - \ref SysTimer_GetSsipValue
 */
__STATIC_FORCEINLINE void SysTimer_SetSsipValue(uint32_t ssip)
{
    unsigned long hartid = SysTimer_GetHartID();
    SysTimer_SetHartSsipValue(ssip, hartid);
}

/**
 * \brief  send ipi to target hart using Systimer Clint SSIP
 * \details
 * This function send ipi using clint timer's sSIP register.
 * \param [in]  hart  target hart
 */
__STATIC_FORCEINLINE void SysTimer_SendIPI_S(unsigned long hartid)
{
    uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
    __SW(addr, 1);
}

/**
 * \brief  clear ipi to target hart using Systimer Clint SSIP
 * \details
 * This function clear ipi using clint timer's SSIP register.
 * \param [in]  hart  target hart
 */
__STATIC_FORCEINLINE void SysTimer_ClearIPI_S(unsigned long hartid)
{
    uint8_t *addr = (uint8_t *)(SysTimer_CLINT_SSIP_BASE(hartid));
    __SW(addr, 0);
}

/**
 * \brief  Enable SSTC access right for supervisor mode
 * \details
 * This will enable SSTC stimecmp(h) csr register read/write access right in supervisor mode
 * and make time(h) csr can be read
 * \attention  This can be only executed in machine mode
 */
__STATIC_FORCEINLINE void SysTimer_EnableSSTC(void)
{
    __RV_CSR_SET(CSR_MCOUNTEREN, MCOUNTEREN_TIME);
#if __RISCV_XLEN == 32
    __RV_CSR_SET(CSR_MENVCFGH, MENVCFGH_STCE);
#else
    __RV_CSR_SET(CSR_MENVCFG, MENVCFG_STCE);
#endif
}

/**
 * \brief  Disable SSTC stimecmp csr access right for supervisor mode
 * \details
 * This will disable SSTC stimecmp(h) csr register read/write access right in supervisor mode
 * and make time(h) csr can not be read
 */
__STATIC_FORCEINLINE void SysTimer_DisableSSTC(void)
{
    __RV_CSR_CLEAR(CSR_MCOUNTEREN, MCOUNTEREN_TIME);
#if __RISCV_XLEN == 32
    __RV_CSR_CLEAR(CSR_MENVCFGH, MENVCFGH_STCE);
#else
    __RV_CSR_CLEAR(CSR_MENVCFG, MENVCFG_STCE);
#endif
}
#endif

/**
 * \brief  Do software reset request
 * \details
 * This function will do software reset request through MTIMER
 * - Software need to write \ref SysTimer_MSFRST_KEY to generate software reset request
 * - The software request flag can be cleared by reset operation to clear
 * \remarks
 * - The software reset is sent to SoC, SoC need to generate reset signal and send back to Core
 * - This function will not return, it will do while(1) to wait the Core reset happened
 */
__STATIC_FORCEINLINE void SysTimer_SoftwareReset(void)
{
    SysTimer->MSFTRST = SysTimer_MSFRST_KEY;
    // will reset cpu, never return
    while (1);
}

/**
 * \brief  send ipi to target hart using Systimer Clint MSIP
 * \details
 * This function send ipi using clint timer's MSIP register.
 * \param [in]  hart  target hart
 */
__STATIC_FORCEINLINE void SysTimer_SendIPI(unsigned long hartid)
{
    uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
    __SW(addr, 1);
}

/**
 * \brief  clear ipi to target hart using Systimer Clint MSIP
 * \details
 * This function clear ipi using clint timer's MSIP register.
 * \param [in]  hart  target hart
 */
__STATIC_FORCEINLINE void SysTimer_ClearIPI(unsigned long hartid)
{
    uint8_t *addr = (uint8_t *)(SysTimer_CLINT_MSIP_BASE(hartid));
    __SW(addr, 0);
}

/**
 * \brief  Enable supervisor mode systimer register read/write access right
 * \details
 * This will make some systimer registers can be accessed in supervisor mode, which is reset state.
 * \attention  This can be only executed in machine mode
 */
__STATIC_FORCEINLINE void SysTimer_EnableSAccess(void)
{
    SysTimer->MTIME_SRW_CTRL = 0;
}

/**
 * \brief  Disable supervisor mode systimer register read/write access right
 * \details
 * This will make some systimer registers can not be accessed in supervisor mode.
 * \attention  This can be only executed in machine mode
 */
__STATIC_FORCEINLINE void SysTimer_DisableSAccess(void)
{
    SysTimer->MTIME_SRW_CTRL = 1;
}

#if defined (__Vendor_SysTickConfig) && (__Vendor_SysTickConfig == 0U)

/**
 * \brief   System Tick Configuration
 * \details Initializes the System Timer and its non-vector interrupt, and starts the System Tick Timer.
 *
 *  In our default implementation, the timer counter will be set to zero, and it will start a timer compare non-vector interrupt
 *  when it matchs the ticks user set, during the timer interrupt user should reload the system tick using \ref SysTick_Reload function
 *  or similar function written by user, so it can produce period timer interrupt.
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \return          0  Function succeeded.
 * \return          1  Function failed.
 * \remarks
 * - For \ref __NUCLEI_N_REV >= 0x0104, the CMPCLREN bit in MTIMECTL is introduced,
 *   but we assume that the CMPCLREN bit is set to 0, so MTIMER register will not be
 *   auto cleared to 0 when MTIMER >= MTIMERCMP.
 * - When the variable \ref __Vendor_SysTickConfig is set to 1, then the
 *   function \ref SysTick_Config is not included.
 * - In this case, the file <b><Device>.h</b> must contain a vendor-specific implementation
 *   of this function.
 * - If user need this function to start a period timer interrupt, then in timer interrupt handler
 *   routine code, user should call \ref SysTick_Reload with ticks to reload the timer.
 * - This function only available when __SYSTIMER_PRESENT == 1 and __ECLIC_PRESENT == 1 and __Vendor_SysTickConfig == 0
 * \sa
 * - \ref SysTimer_SetCompareValue; SysTimer_SetLoadValue
 */
__STATIC_INLINE uint32_t SysTick_Config(uint64_t ticks)
{
    uint64_t loadticks = SysTimer_GetLoadValue();
    SysTimer_SetCompareValue(ticks + loadticks);

#if defined(__ECLIC_PRESENT) && (__ECLIC_PRESENT == 1)
    ECLIC_SetShvIRQ(SysTimer_IRQn, ECLIC_NON_VECTOR_INTERRUPT);
    ECLIC_SetLevelIRQ(SysTimer_IRQn, 0);
    ECLIC_EnableIRQ(SysTimer_IRQn);
#endif
    return (0UL);
}

/**
 * \brief   System Tick Configuration By hartid
 * \details Initializes the System Timer and its non-vector interrupt, and starts the System Tick Timer.
 *
 *  In our default implementation, the timer counter will be set to zero, and it will start a timer compare non-vector interrupt
 *  when it matchs the ticks user set, during the timer interrupt user should reload the system tick using \ref SysTick_Reload function
 *  or similar function written by user, so it can produce period timer interrupt.
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \return          0  Function succeeded.
 * \return          1  Function failed.
 * \remarks
 * - For \ref __NUCLEI_N_REV >= 0x0104, the CMPCLREN bit in MTIMECTL is introduced,
 *   but we assume that the CMPCLREN bit is set to 0, so MTIMER register will not be
 *   auto cleared to 0 when MTIMER >= MTIMERCMP.
 * - When the variable \ref __Vendor_SysTickConfig is set to 1, then the
 *   function \ref SysTick_Config is not included.
 * - In this case, the file <b><Device>.h</b> must contain a vendor-specific implementation
 *   of this function.
 * - If user need this function to start a period timer interrupt, then in timer interrupt handler
 *   routine code, user should call \ref SysTick_Reload with ticks to reload the timer.
 * - This function only available __Vendor_SysTickConfig == 0
 * - When ECLIC present, it will set eclic timer interrupt as non-vector mode, and level configured to 0, and enable it
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * \sa
 * - \ref SysTimer_SetCompareValue; SysTimer_SetLoadValue
 */
__STATIC_INLINE uint32_t SysTick_HartConfig(uint64_t ticks, unsigned long hartid)
{
    uint64_t loadticks = SysTimer_GetLoadValue();
    SysTimer_SetHartCompareValue(ticks + loadticks, hartid);

#if defined(__ECLIC_PRESENT) && (__ECLIC_PRESENT == 1)
    ECLIC_SetShvIRQ(SysTimer_IRQn, ECLIC_NON_VECTOR_INTERRUPT);
    ECLIC_SetLevelIRQ(SysTimer_IRQn, 0);
    ECLIC_EnableIRQ(SysTimer_IRQn);
#endif
    return (0UL);
}

/**
 * \brief   System Tick Reload
 * \details Reload the System Timer Tick when the MTIMECMP reached TIME value
 *
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \return          0  Function succeeded.
 * \return          1  Function failed.
 * \remarks
 * - For \ref __NUCLEI_N_REV >= 0x0104, the CMPCLREN bit in MTIMECTL is introduced,
 *   but for this \ref SysTick_Config function, we assume this CMPCLREN bit is set to 0,
 *   so in interrupt handler function, user still need to set the MTIMERCMP or MTIMER to reload
 *   the system tick, if vendor want to use this timer's auto clear feature, they can define
 *   \ref __Vendor_SysTickConfig to 1, and implement \ref SysTick_Config and \ref SysTick_Reload functions.
 * - When the variable \ref __Vendor_SysTickConfig is set to 1, then the
 *   function \ref SysTick_Reload is not included.
 * - In this case, the file <b><Device>.h</b> must contain a vendor-specific implementation
 *   of this function.
 * - This function only available when __SYSTIMER_PRESENT == 1
 * - Since the MTIMERCMP value might overflow, if overflowed, MTIMER will be set to 0, and MTIMERCMP set to ticks
 * \sa
 * - \ref SysTimer_SetCompareValue
 * - \ref SysTimer_SetLoadValue
 */
__STATIC_INLINE uint32_t SysTick_Reload(uint64_t ticks)
{
    uint64_t cur_ticks = SysTimer_GetLoadValue();

    uint64_t reload_ticks = ticks + cur_ticks;

    SysTimer_SetCompareValue(reload_ticks);

    return (0UL);
}

/**
 * \brief   System Tick Reload By hartid
 * \details Reload the System Timer Tick when the MTIMECMP reached TIME value
 *
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \param [in]  hartid  hart ID, one hart is required to have a known hart ID of 0, other harts ID can be in 1~1023.
 * \return          0  Function succeeded.
 * \return          1  Function failed.
 * \remarks
 * - For \ref __NUCLEI_N_REV >= 0x0104, the CMPCLREN bit in MTIMECTL is introduced,
 *   but for this \ref SysTick_Config function, we assume this CMPCLREN bit is set to 0,
 *   so in interrupt handler function, user still need to set the MTIMERCMP or MTIMER to reload
 *   the system tick, if vendor want to use this timer's auto clear feature, they can define
 *   \ref __Vendor_SysTickConfig to 1, and implement \ref SysTick_Config and \ref SysTick_Reload functions.
 * - When the variable \ref __Vendor_SysTickConfig is set to 1, then the
 *   function \ref SysTick_Reload is not included.
 * - In this case, the file <b><Device>.h</b> must contain a vendor-specific implementation
 *   of this function.
 * - This function only available when __SYSTIMER_PRESENT == 1 and __ECLIC_PRESENT == 1 and __Vendor_SysTickConfig == 0
 * - Since the MTIMERCMP value might overflow, if overflowed, MTIMER will be set to 0, and MTIMERCMP set to ticks
 * - In S-mode, hartid can't be get by using __get_hart_id function, so this api suits S-mode particularly.
 * \sa
 * - \ref SysTimer_SetCompareValue
 * - \ref SysTimer_SetLoadValue
 */
__STATIC_INLINE uint32_t SysTick_HartReload(uint64_t ticks, unsigned long hartid)
{
    uint64_t cur_ticks = SysTimer_GetLoadValue();
    uint64_t reload_ticks = ticks + cur_ticks;

    SysTimer_SetHartCompareValue(reload_ticks, hartid);

    return (0UL);
}

#if defined(__SSTC_PRESENT) && (__SSTC_PRESENT == 1)
/**
 * \brief   System Tick Configuration in supervisor mode
 * \details Initializes the system timer supervisor mode interrupt and registered as non-vector interrupt
 *
 *  The smode timecmp csr register will be set to proper value according to the ticks passed
 *  when it matchs the ticks user set, during the smode timer interrupt user should reload the system tick using \ref SysTick_Reload_S function
 *  or similar function written by user, so it can produce period smode timer interrupt.
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \return          0  Function succeeded.
 */
__STATIC_INLINE uint32_t SysTick_Config_S(uint64_t ticks)
{
    uint64_t loadticks = __get_rv_time();
    SysTimer_SetCompareValue_S(ticks + loadticks);

#if defined(__ECLIC_PRESENT) && (__ECLIC_PRESENT == 1)
#if defined(__TEE_PRESENT) && (__TEE_PRESENT == 1)
    ECLIC_SetShvIRQ_S(SysTimer_S_IRQn, ECLIC_NON_VECTOR_INTERRUPT);
    ECLIC_SetLevelIRQ_S(SysTimer_S_IRQn, 0);
    ECLIC_EnableIRQ_S(SysTimer_S_IRQn);
#endif
#endif
    return (0UL);
}

/**
 * \brief   System Tick Reload in supervisor mode
 * \details Reload the System Timer Tick when the STIMECMP CSR reached TIME value
 *
 * \param [in]  ticks  Number of ticks between two interrupts.
 * \return          0  Function succeeded.
 * \return          1  Function failed.
 */
__STATIC_INLINE uint32_t SysTick_Reload_S(uint64_t ticks)
{
    uint64_t cur_ticks = __get_rv_time();

    uint64_t reload_ticks = ticks + cur_ticks;

    SysTimer_SetCompareValue_S(reload_ticks);

    return (0UL);
}
#endif

#endif /* defined(__Vendor_SysTickConfig) && (__Vendor_SysTickConfig == 0U) */
/** @} */ /* End of Doxygen Group NMSIS_Core_SysTimer */

#endif /* defined(__SYSTIMER_PRESENT) && (__SYSTIMER_PRESENT == 1) */

#ifdef __cplusplus
}
#endif
#endif /* __CORE_FEATURE_TIMER_H__ */
