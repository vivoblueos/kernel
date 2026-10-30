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
#ifndef __CORE_FEATURE_PLIC__
#define __CORE_FEATURE_PLIC__
/*!
 * @file     core_feature_plic.h
 * @brief    PLIC feature API header file for RISC-V Core
 */
/*
 * PLIC Feature Configuration Macro:
 * 1. __PLIC_PRESENT:  Define whether Platform Level Interrupt Controller (PLIC) Unit is present or not
 *   * 0: Not present
 *   * 1: Present
 * 2. __PLIC_BASEADDR:  Base address of the PLIC unit.
 * 3. __PLIC_INTNUM  : Define the external interrupt number of PLIC Unit
 *
 */
#ifdef __cplusplus
 extern "C" {
#endif

#include "core_feature_base.h"

#if defined(__PLIC_PRESENT) && (__PLIC_PRESENT == 1)
/**
 * \defgroup NMSIS_Core_PLIC_Registers     Register Define and Type Definitions Of PLIC
 * \ingroup NMSIS_Core_Registers
 * \brief   Type definitions and defines for plic registers.
 *
 * @{
 */

/* 32 bits per source */
#define PLIC_PRIORITY_OFFSET                _AC(0x0000,UL)      /*!< PLIC Priority register offset */
#define PLIC_PRIORITY_SHIFT_PER_SOURCE      2                   /*!< PLIC Priority register offset shift per source */
/* 1 bit per source (1 address) */
#define PLIC_PENDING_OFFSET                 _AC(0x1000,UL)      /*!< PLIC Pending register offset */
#define PLIC_PENDING_SHIFT_PER_SOURCE       0                   /*!< PLIC Pending register offset shift per source */

/* 0x80 per context */
#define PLIC_ENABLE_OFFSET                  _AC(0x2000,UL)      /*!< PLIC Enable register offset */
#define PLIC_ENABLE_SHIFT_PER_CONTEXT       7                   /*!< PLIC Enable register offset shift per context */

#define PLIC_THRESHOLD_OFFSET               _AC(0x200000,UL)    /*!< PLIC Threshold register offset */
#define PLIC_CLAIM_OFFSET                   _AC(0x200004,UL)    /*!< PLIC Claim register offset */
#define PLIC_THRESHOLD_SHIFT_PER_CONTEXT    12                  /*!< PLIC Threshold register offset shift per context */
#define PLIC_CLAIM_SHIFT_PER_CONTEXT        12                  /*!< PLIC Claim register offset shift per context */

#ifndef __PLIC_BASEADDR
/* Base address of PLIC(__PLIC_BASEADDR) should be defined in <Device.h> */
#error "__PLIC_BASEADDR is not defined, please check!"
#endif

/* PLIC Memory mapping of Device */
#define PLIC_BASE                           __PLIC_BASEADDR     /*!< PLIC Base Address */

/**
 * PLIC_GetHartID() is used to get plic hartid which might not be the same as cpu hart id,
 * for example, cpu hartid may be 1, but plic hartid may be 0, then plic hartid offset is 1.
 * If defined __PLIC_HARTID, it will use __PLIC_HARTID as plic hartid,
 * otherwise, it will use __get_hart_index().
 * The cpu hartid is get by using __get_hart_id function
 */
#ifndef __PLIC_HARTID
#define PLIC_GetHartID()                    (__get_hart_index())
#define PLIC_GetHartID_S()                  (__get_hart_index_s())
#else
#define PLIC_GetHartID()                    (__PLIC_HARTID)
#define PLIC_GetHartID_S()                  (__PLIC_HARTID)
#endif

#define PLIC_GetHartMContextID()            (PLIC_GetHartID() << 1)
// TODO SMODE HARTID need to handle, maybe use a predefined variable of hartid
#define PLIC_GetHartSContextID()            ((PLIC_GetHartID_S() << 1) + 1)

#define PLIC_PRIORITY_REGADDR(source)       ((PLIC_BASE) + (PLIC_PRIORITY_OFFSET)  + ((source) << PLIC_PRIORITY_SHIFT_PER_SOURCE))
#define PLIC_PENDING_REGADDR(source)        ((PLIC_BASE) + (PLIC_PENDING_OFFSET)   + (((source) >> 5) * 4))
#define PLIC_ENABLE_REGADDR(ctxid, source)  ((PLIC_BASE) + (PLIC_ENABLE_OFFSET)    + ((ctxid) << PLIC_ENABLE_SHIFT_PER_CONTEXT) + ((source) >> 5) * 4)
#define PLIC_THRESHOLD_REGADDR(ctxid)       ((PLIC_BASE) + (PLIC_THRESHOLD_OFFSET) + ((ctxid) << PLIC_THRESHOLD_SHIFT_PER_CONTEXT))
#define PLIC_CLAIM_REGADDR(ctxid)           ((PLIC_BASE) + (PLIC_CLAIM_OFFSET) + ((ctxid) << PLIC_CLAIM_SHIFT_PER_CONTEXT))
#define PLIC_COMPLETE_REGADDR(ctxid)        (PLIC_CLAIM_REGADDR(ctxid))


/** @} */ /* end of group NMSIS_Core_PLIC_Registers */

/* ##########################   PLIC functions  #################################### */
/**
 * \defgroup   NMSIS_Core_IntPlic        PLIC Interrupt
 * \brief Functions that manage interrupts via the PLIC.
 *
 * @{
 */

/**
 * \brief  Set priority threshold value of plic for selected context
 * \details
 * This function set priority threshold value of plic for selected context.
 * \param [in]    ctxid     selected context id
 * \param [in]    thresh    threshold value
 * \remarks
 * \sa
 * - \ref PLIC_GetContextThreshold
 */
__STATIC_FORCEINLINE void PLIC_SetContextThreshold(uint32_t ctxid, uint32_t thresh)
{
    volatile uint32_t *thresh_reg = (uint32_t *)PLIC_THRESHOLD_REGADDR(ctxid);

    *thresh_reg = thresh;
}

/**
 * \brief  Get priority threshold value of plic for selected context
 * \details
 * This function get priority threshold value of plic for selected context.
 * \param [in]    ctxid     selected context id
 * \return priority threshold value for selected context
 * \remarks
 * \sa
 * - \ref PLIC_SetContextThreshold
 */
__STATIC_FORCEINLINE uint32_t PLIC_GetContextThreshold(uint32_t ctxid)
{
    volatile uint32_t *thresh_reg = (uint32_t *)PLIC_THRESHOLD_REGADDR(ctxid);

    return (*thresh_reg);
}

/**
 * \brief  Enable interrupt of selected source plic for selected context
 * \details
 * This function enable interrupt of selected source plic for selected context.
 * \param [in]    ctxid     selected context id
 * \param [in]    source    interrupt source
 * \remarks
 * \sa
 * - \ref PLIC_DisableContextInterrupt
 */
__STATIC_FORCEINLINE void PLIC_EnableContextInterrupt(uint32_t ctxid, uint32_t source)
{
    volatile uint32_t *enable_reg = (uint32_t *)PLIC_ENABLE_REGADDR(ctxid, source);

    uint32_t current = *enable_reg;
    current = current | (1UL << (source & 0x1F));
    *enable_reg = current;
}

/**
 * \brief  Disable interrupt of selected source plic for selected context
 * \details
 * This function disable interrupt of selected source plic for selected context
 * \param [in]    ctxid     selected context id
 * \param [in]    source    interrupt source
 * \remarks
 * \sa
 * - \ref PLIC_EnableContextInterrupt
 */
__STATIC_FORCEINLINE void PLIC_DisableContextInterrupt(uint32_t ctxid, uint32_t source)
{
    volatile uint32_t *enable_reg = (uint32_t *)PLIC_ENABLE_REGADDR(ctxid, source);

    uint32_t current = *enable_reg;
    current = current & (~(1UL << (source & 0x1F)));
    *enable_reg = current;
}

/**
 * \brief  Get interrupt enable status of selected source plic for selected context
 * \details
 * This function get interrupt enable of selected source plic for selected context.
 * \param [in]    ctxid     selected context id
 * \param [in]    source    interrupt source
 * \return enable status for selected interrupt source for selected context
 * \remarks
 * \sa
 * - \ref PLIC_EnableContextInterrupt
 * - \ref PLIC_DisableContextInterrupt
 */
__STATIC_FORCEINLINE uint32_t PLIC_GetContextInterruptEnable(uint32_t ctxid, uint32_t source)
{
    volatile uint32_t *enable_reg = (uint32_t *)PLIC_ENABLE_REGADDR(ctxid, source);

    uint32_t current = *enable_reg;
    current = (current >> (source & 0x1F)) & 0x1;
    return current;
}

/**
 * \brief  Set interrupt pending of selected source plic
 * \details
 * This function set interrupt pending of selected source plic.
 * \param [in]    source    interrupt source
 * \remarks
 * \sa
 * - \ref PLIC_GetInterruptPending
 * - \ref PLIC_CLearInterruptPending
 */
__STATIC_FORCEINLINE void PLIC_SetInterruptPending(uint32_t source)
{
    volatile uint32_t *pending_reg = (uint32_t *)PLIC_PENDING_REGADDR(source);

    uint32_t current = *pending_reg;
    current = current | (1UL << (source & 0x1F));
    *pending_reg = current;
}

/**
 * \brief  Clear interrupt pending of selected source plic
 * \details
 * This function clear interrupt pending of selected source plic
 * \param [in]    source    interrupt source
 * \remarks
 * \sa
 * - \ref PLIC_SetInterruptPending
 * - \ref PLIC_GetInterruptPending
 */
__STATIC_FORCEINLINE void PLIC_ClearInterruptPending(uint32_t source)
{
    volatile uint32_t *pending_reg = (uint32_t *)PLIC_PENDING_REGADDR(source);

    uint32_t current = *pending_reg;
    current = current & (~(1UL << (source & 0x1F)));
    *pending_reg = current;
}

/**
 * \brief  Get interrupt pending status of selected source plic
 * \details
 * This function get interrupt pending of selected source plic
 * \param [in]    source    interrupt source
 * \return interrupt pending status for selected interrupt source
 * \remarks
 * \sa
 * - \ref PLIC_SetInterruptPending
 * - \ref PLIC_ClearInterruptPending
 */
__STATIC_FORCEINLINE uint32_t PLIC_GetInterruptPending(uint32_t source)
{
    volatile uint32_t *pending_reg = (uint32_t *)PLIC_PENDING_REGADDR(source);

    uint32_t current = *pending_reg;
    current = (current >> (source & 0x1F)) & 0x1;
    return current;
}

/**
 * \brief  Set interrupt priority for selected source plic
 * \details
 * This function set interrupt priority for selected source plic.
 * \param [in]    source    interrupt source
 * \param [in]    priority  interrupt priority
 * \remarks
 * \sa
 * - \ref PLIC_GetPriority
 */
__STATIC_FORCEINLINE void PLIC_SetPriority(uint32_t source, uint32_t priority)
{
    volatile uint32_t *priority_reg = (uint32_t *)PLIC_PRIORITY_REGADDR(source);

    *priority_reg = priority;
}

/**
 * \brief  Get interrupt priority for selected source plic
 * \details
 * This function get interrupt priority for selected source plic.
 * \param [in]    source    interrupt source
 * \param [in]    priority  interrupt priority
 * \remarks
 * \sa
 * - \ref PLIC_SetPriority
 */
__STATIC_FORCEINLINE uint32_t PLIC_GetPriority(uint32_t source)
{
    volatile uint32_t *priority_reg = (uint32_t *)PLIC_PRIORITY_REGADDR(source);

    return (*priority_reg);
}

/**
 * \brief  Claim interrupt for plic for selected context
 * \details
 * This function claim interrupt for plic for selected context.
 * \param [in]    ctxid     selected context id
 * \return  the ID of the highest priority pending interrupt or
 *      zero if there is no pending interrupt
 * \remarks
 * A successful claim will also atomically clear the corresponding pending bit
 * on the interrupt source. The PLIC can perform a claim at any time and the
 * claim operation is not affected by the setting of the priority threshold register.
 * \sa
 * - \ref PLIC_CompleteContextInterrupt
 */
__STATIC_FORCEINLINE uint32_t PLIC_ClaimContextInterrupt(uint32_t ctxid)
{
    volatile uint32_t *claim_reg = (uint32_t *)PLIC_CLAIM_REGADDR(ctxid);

    return (*claim_reg);
}

/**
 * \brief  Complete interrupt for plic for selected context
 * \details
 * This function complete interrupt for plic for selected context.
 * \param [in]    ctxid     selected context id
 * \return  the ID of the highest priority pending interrupt or
 *      zero if there is no pending interrupt
 * \remarks
 * The PLIC signals it has completed executing an interrupt handler by writing
 * the interrupt ID it received from the claim to the claim/complete register.
 * The PLIC does not check whether the completion ID is the same as the last
 * claim ID for that context.
 * If the completion ID does not match an interrupt source that is currently
 * enabled for the context, the completion is silently ignored.
 * \sa
 * - \ref PLIC_ClaimContextInterrupt
 */
__STATIC_FORCEINLINE void PLIC_CompleteContextInterrupt(uint32_t ctxid, uint32_t source)
{
    volatile uint32_t *complete_reg = (uint32_t *)PLIC_COMPLETE_REGADDR(ctxid);

    *complete_reg = source;
}

/**
 * \brief  Perform init for plic for selected context
 * \details
 * This function perform initialization steps for plic for selected context.
 * \param [in]    ctxid           selected context id
 * \param [in]    num_sources     plic interrupt source count number
 * \param [in]    enable          plic interrupt enable or not
 * \param [in]    thresh          plic interrupt threshold
 * \remarks
 * * Disable all interrupts
 * * Set priority threshold to value specified by thresh
 */
__STATIC_INLINE void PLIC_Context_Init(uint32_t ctxid, uint32_t num_sources, uint32_t enable, uint32_t thresh)
{
    uint32_t i;

    for (i = 0; i < num_sources; i ++) {
        if (enable) {
            PLIC_EnableContextInterrupt(ctxid, i);
        } else {
            PLIC_DisableContextInterrupt(ctxid, i);
        }
    }
    PLIC_SetContextThreshold(ctxid, thresh);
}

#define PLIC_Init(num_sources, enable, thresh)          PLIC_Context_Init(PLIC_GetHartMContextID(), (num_sources), (enable), (thresh))
#define PLIC_Init_S(num_sources, enable, thresh)        PLIC_Context_Init(PLIC_GetHartSContextID(), (num_sources), (enable), (thresh))

#define PLIC_ClaimInterrupt()                           PLIC_ClaimContextInterrupt(PLIC_GetHartMContextID())
#define PLIC_ClaimInterrupt_S()                         PLIC_ClaimContextInterrupt(PLIC_GetHartSContextID())

#define PLIC_CompleteInterrupt(source)                  PLIC_CompleteContextInterrupt(PLIC_GetHartMContextID(), (source))
#define PLIC_CompleteInterrupt_S(source)                PLIC_CompleteContextInterrupt(PLIC_GetHartSContextID(), (source))

#define PLIC_GetInterruptEnable(source)                 PLIC_GetContextInterruptEnable(PLIC_GetHartMContextID(), (source))
#define PLIC_GetInterruptEnable_S(source)               PLIC_GetContextInterruptEnable(PLIC_GetHartSContextID(), (source))

#define PLIC_EnableInterrupt(source)                    PLIC_EnableContextInterrupt(PLIC_GetHartMContextID(), (source))
#define PLIC_EnableInterrupt_S(source)                  PLIC_EnableContextInterrupt(PLIC_GetHartSContextID(), (source))

#define PLIC_DisableInterrupt(source)                   PLIC_DisableContextInterrupt(PLIC_GetHartMContextID(), (source))
#define PLIC_DisableInterrupt_S(source)                 PLIC_DisableContextInterrupt(PLIC_GetHartSContextID(), (source))

#define PLIC_SetThreshold(source, thresh)               PLIC_SetContextThreshold(PLIC_GetHartMContextID(), (source), (thresh))
#define PLIC_SetThreshold_S(source, thresh)             PLIC_SetContextThreshold(PLIC_GetHartSContextID(), (source), (thresh))

#define PLIC_GetThreshold()                             PLIC_GetContextThreshold(PLIC_GetHartMContextID())
#define PLIC_GetThreshold_S()                           PLIC_GetContextThreshold(PLIC_GetHartSContextID())

/**
 * \brief  Set Trap entry address
 * \details
 * This function set trap entry address to 'CSR_MTVEC'.
 * \param [in]      addr  trap entry address
 * \remarks
 * - This function use to set trap entry address to 'CSR_MTVEC'.
 * \sa
 * - \ref __get_trap_entry
 */
__STATIC_FORCEINLINE void __set_trap_entry(rv_csr_t addr)
{
    addr &= (rv_csr_t)(~0x7);
    __RV_CSR_WRITE(CSR_MTVEC, addr);
}

/**
 * \brief  Get trap entry address
 * \details
 * This function get trap entry address from 'CSR_MTVEC'.
 * \return       trap entry address
 * \remarks
 * - This function use to get trap entry address from 'CSR_MTVEC'.
 * \sa
 * - \ref __set_trap_entry
 */
__STATIC_FORCEINLINE rv_csr_t __get_trap_entry(void)
{
    unsigned long addr = __RV_CSR_READ(CSR_MTVEC);
    return (addr);
}

/** @} */ /* End of Doxygen Group NMSIS_Core_IntExc */

#endif /* defined(__PLIC_PRESENT) && (__PLIC_PRESENT == 1) */

#ifdef __cplusplus
}
#endif
#endif /** __CORE_FEATURE_PLIC__ */
