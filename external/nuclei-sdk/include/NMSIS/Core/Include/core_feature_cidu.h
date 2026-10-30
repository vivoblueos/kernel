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
#ifndef __CORE_FEATURE_CIDU_H__
#define __CORE_FEATURE_CIDU_H__
/*!
 * @file     core_feature_cidu.h
 * @brief    Cluster Interrupt Distribution Unit feature API header file for Nuclei N/NX Core
 */
/*
 * CIDU Feature Configuration Macro:
 * 1. __CIDU_PRESENT:  Define whether Cluster Interrupt Distribution Unit is present or not.
 *   * 0: Not present
 *   * 1: Present
 * 2. __CIDU_BASEADDR:  Define the base address of the CIDU.
 */
#ifdef __cplusplus
extern "C" {
#endif

#include "core_feature_base.h"

#if defined(__CIDU_PRESENT) && (__CIDU_PRESENT == 1)

/* ##########################  CIDU functions  #################################### */
/**
 * \defgroup NMSIS_Core_CIDU         CIDU Functions
 * \ingroup  NMSIS_Core
 * \brief    Functions that manage external interrupts, inter core interrupts and semaphores.
 * \details
 *
 * Nuclei provide Cluster Interrupt Distribution Unit (CIDU) for scenarios that a SMP system is designed for real
 * time application or both Linux and real time application, and Nuclei processor core can optionally support CIDU.
 * The CIDU is used to distribute external interrupts to the core’s ECLIC, also it provides Inter Core Interrupt (ICI)
 * and Semaphores Mechanism. Its features are as follows:
 *
 * * Support up to 16 Cores in one cluster
 * * Support up to 4096 external interrupts sources
 * * Support up to 16 Inter Core Interrupts
 * * Support 32 Semaphores
 *
 *   @{
 */

#ifndef __CIDU_BASEADDR
/* Base address of CIDU(__CIDU_BASEADDR) should be defined in <Device.h> */
#error "__CIDU_BASEADDR is not defined, please check!"
#endif

#define CIDU_BASE                                __CIDU_BASEADDR
#define CIDU_RECEIVE_INTERRUPT_EN(core_id)       (0x1UL << core_id)   /*!< Indicates the core can receive corresponding interrupt */

#define CIDU_CORE_INT_STATUS_OFS      0x0        /*!< Core n Inter Core Interrupt status register base offset */
#define CIDU_SEMAPHORE_OFS            0x80       /*!< Semaphore n register base offset */
#define CIDU_ICI_SHADOW_OFS           0x3FFC     /*!< ICI Interrupt source core ID and target core ID register offset */
#define CIDU_INT_INDICATOR_OFS        0x4000     /*!< External interrupt n indicator register base offset */
#define CIDU_INT_MASK_OFS             0x8000     /*!< External interrupt n mask (mask interrupt n to cores or not when interrupt n indicator on)register base offset */
#define CIDU_CORE_NUM_OFS             0xC084     /*!< Static configuration core num register offset */
#define CIDU_INT_NUM_OFS              0xC090     /*!< Static configuration external interrupt number register offset */

#define CIDU_CORE_INT_STATUS_ADDR(n)  (unsigned long)((CIDU_BASE) + (CIDU_CORE_INT_STATUS_OFS) + ((n) << 2))    /*!< Core n Inter Core Interrupt status register address */
#define CIDU_SEMAPHORE_ADDR(n)        (unsigned long)((CIDU_BASE) + (CIDU_SEMAPHORE_OFS) + ((n) << 2))          /*!< Semaphore n register address */
#define CIDU_ICI_SHADOW_ADDR          (unsigned long)((CIDU_BASE) + (CIDU_ICI_SHADOW_OFS))                      /*!< ICI Interrupt source core ID and target core ID register address */
#define CIDU_INT_INDICATOR_ADDR(n)    (unsigned long)((CIDU_BASE) + (CIDU_INT_INDICATOR_OFS) + ((n) << 2))      /*!< External interrupt n indicator register address */
#define CIDU_INT_MASK_ADDR(n)         (unsigned long)((CIDU_BASE) + (CIDU_INT_MASK_OFS) + ((n) << 2))           /*!< External interrupt n mask (mask interrupt n to cores or not when interrupt n indicator on)register address */
#define CIDU_CORE_NUM_ADDR            (unsigned long)((CIDU_BASE) + (CIDU_CORE_NUM_OFS))                        /*!< Static configuration core num register address */
#define CIDU_INT_NUM_ADDR             (unsigned long)((CIDU_BASE) + (CIDU_INT_NUM_OFS))                         /*!< Static configuration external interrupt number register address */


/* SEND_CORE_ID position in ICI_SHADOW_REG register */
#define CIDU_ICI_SEND_CORE_ID_POS     16

/**
 * \brief  Get core number in the cluster
 * \details
 * Indicate the static configuration core num in the cluster.
 * \return core number configured
 * \remarks
 * - In a Nulcei multi-core system, each core has an identifiable serial number, the serial number starts from 0 and is
 *   continuous, also the number is static.
 * - CORE_NUM register is read only.
*/
__STATIC_FORCEINLINE uint32_t CIDU_GetCoreNum(void)
{
    uint32_t val;
    uint32_t* addr = (uint32_t*)CIDU_CORE_NUM_ADDR;

    val = __LW(addr);
    return val;
}

/**
 * \brief  Get external interrupt number
 * \details
 * Indicate the static configuration external interrupt number
 * \return interrupt number configured
 * \remarks
 * - INT_NUM register is read only.
*/
__STATIC_FORCEINLINE uint32_t CIDU_GetIntNum(void)
{
    uint32_t val;
    uint32_t* addr = (uint32_t*)CIDU_INT_NUM_ADDR;

    val = __LW(addr);
    return val;
}
/** @} */ /* End of Doxygen Group NMSIS_Core_CIDU */

/**
 * \defgroup NMSIS_Core_Distribute_Interrupt      External Interrupt Distribution Functions
 * \ingroup  NMSIS_Core_CIDU
 * \brief    Functions that distribute external interrupts to cores.
 * @{
 */

/**
 * \brief  Broadcast external interrupt to cores
 * \details
 * This function broadcasts external interrupt which id is int_id to some/all target cores
 * \param [in]    int_id      external interrupt id
 * \param [in]    to_cores    target cores which can receive interrupt, use bitwise inclusive or
 *                            of \ref CIDU_RECEIVE_INTERRUPT_EN(core_id)
 * \remarks
 * - External IRQn ID(int_id) is from the hard-wired persperctive,
 *   which has an offset mapped to the ECLIC IRQn, see Interrupt Number Definition in <Device.h>
 * - By default on reset, only core 0 can receive interrupt which id is int_id
*/
__STATIC_FORCEINLINE void CIDU_BroadcastExtInterrupt(uint32_t int_id, uint32_t to_cores)
{
    uint32_t* addr = (uint32_t*)CIDU_INT_INDICATOR_ADDR(int_id);

    __SW(addr, (uint32_t)to_cores);
}

/**
 * \brief  get broadcast mode status
 * \details
 * Just query the INTn_INDICATOR register value
 * \param [in]    int_id    external interrupt id
 * \return INTn_INDICATOR register value
 * \remarks
 * - External IRQn ID(int_id) is from the hard-wired persperctive,
 *   which has an offset mapped to the ECLIC IRQn, see Interrupt Number Definition in <Device.h>
 * - By default on reset, only core 0 can receive interrupt which id is int_id
*/
__STATIC_FORCEINLINE uint32_t CIDU_GetBroadcastModeStatus(uint32_t int_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_INT_INDICATOR_ADDR(int_id);

    val = __LW(addr);
    return val;
}

/**
 * \brief  Let the first coming core to first claim the interrupt
 * \details
 * In external interrupt broadcast mode, make the first coming core to claim this interrupt and then can handle it.
 * \param [in]    int_id     external interrupt id
 * \param [in]    core_id    core id that receive the interrupt
 * \return -1 if it fails to claim the interrupt, else it can continue to handle the interrupt
 * \remarks
 * - External IRQn ID(int_id) is from the hard-wired persperctive,
 *   which has an offset mapped to the ECLIC IRQn, see Interrupt Number Definition in <Device.h>.
 * - If it fails to claim the interrupt, it should quit the interrupt n's handler of all cores
 * - When a core claims the interrupt successfully and has handled it, it must call \ref CIDU_ResetFirstClaimMode to reset the claim.
 * \sa
 * - \ref CIDU_BroadcastExtInterrupt
 * - \ref CIDU_ResetFirstClaimMode
*/
__STATIC_INLINE long CIDU_SetFirstClaimMode(uint32_t int_id, uint32_t core_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_INT_MASK_ADDR(int_id);
    uint32_t mask = 1UL << core_id;

    __SW(addr, mask);
    val = __LW(addr);
    if (mask == val) {
        return 0;
    }
    return -1;
}

/**
 * \brief  Reset the claim mode mask
 * \details
 * Reset the claim mode mask by Writing the reset value (all 1) to it
 * \param [in] int_id    external interrupt id
 * \remarks
 * - External IRQn ID(int_id) is from the hard-wired persperctive,
 *   which has an offset mapped to the ECLIC IRQn, see Interrupt Number Definition in <Device.h>
 * - When a core claims the interrupt successfully and handle it, it must call \ref CIDU_ResetFirstClaimMode to reset the claim
 * \sa
 * - \ref CIDU_SetFirstClaimMode
*/
__STATIC_FORCEINLINE void CIDU_ResetFirstClaimMode(uint32_t int_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_INT_MASK_ADDR(int_id);

    /* clear by writing all 1 */
    __SW(addr, 0xFFFFFFFF);
}

/**
 * \brief  Get the claim mask status
 * \details
 * Get the claim mode staus, each bit[n] indicates whether core n has claimed interrupt successfully,
 * 1 means yes, 0 means no.
 * \param [in]    int_id    external interrupt id
 * \return claim mode register INTn_MASK value
 * \remarks
 * - External IRQn ID(int_id) is from the hard-wired persperctive,
 *   which has an offset mapped to the ECLIC IRQn, see Interrupt Number Definition in <Device.h>
 * \sa
 * - \ref CIDU_ResetFirstClaimMode
 * - \ref CIDU_SetFirstClaimMode
*/
__STATIC_FORCEINLINE uint32_t CIDU_GetClaimStatus(uint32_t int_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_INT_MASK_ADDR(int_id);

    val = __LW(addr);
    return val;
}
/** @} */ /* End of Doxygen Group NMSIS_Core_Distribute_Interrupt */

/**
 * \defgroup NMSIS_Core_ICI      Inter Core Interrupt Functions
 * \ingroup  NMSIS_Core_CIDU
 * \brief    Functions that implement Inter Core Interrupt mechanism.
 * @{
 * Inter Core Interrupt (ICI) means that one core can send interrupt to another core in a multi-core cluster. CIDU ICI belongs
 * to Internal Interrupt.
 *
 * * CIDU ICI Interrupt ID is fixed to 16.
 */

/**
 * \brief  Trigger interrupt to another core in a multi-core cluster
 * \details
 * When called by core send_core_id, CIDU will trigger ICI to core recv_core_id automatically.
 * and core recv_core_id could query \ref CIDU_GetCoreIntSenderId to know the sender.
 * \param [in]    send_core_id    the core id which want to send the inter core interrupt
 * \param [in]    recv_core_id    the core id which will receive the inter core interrupt
 * \remarks
 * - The core recv_core_id need to call CIDU_ClearInterCoreIntReq to clear the corresponding bit/bits
 *   of its own COREn_INT_STATUS.
 * - It supports that multiple cores call \ref CIDU_TriggerInterCoreInt simultaneously.
 * \sa
 * - \ref CIDU_GetCoreIntSenderId
 * - \ref CIDU_ClearInterCoreIntReq
*/
__STATIC_FORCEINLINE void CIDU_TriggerInterCoreInt(uint32_t send_core_id, uint32_t recv_core_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_ICI_SHADOW_ADDR;

    val = (uint32_t)(send_core_id << CIDU_ICI_SEND_CORE_ID_POS) | (uint32_t)(recv_core_id);
    __SW(addr, (uint32_t)val);
}

/**
 * \brief  Core recv_core_id queries out who sends inter core interrupt to itself
 * \details
 * In the ISR of ICI, receive core can query if bit[n] of this return value is 1, core n sends the current ICI,
 * if bit[m] is 1, then core m also sends, etc.
 * \param [in]    recv_core_id    the core id which receives the inter core interrupt
 * \return    Value that shows sender core's ID n whose bit[n](bit[m] if core m send too, etc.) is 1
 * \remarks
 * - If the ICI ISR has finished the job, should call \ref CIDU_ClearInterCoreIntReq to clear the IRQ
*/
__STATIC_FORCEINLINE uint32_t CIDU_QueryCoreIntSenderMask(uint32_t recv_core_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_CORE_INT_STATUS_ADDR(recv_core_id);

    val = __LW(addr);
    return val;
}

/**
 * \brief  Clear the corresponding bit/bits of ICI request triggered by sender core
 * \details
 * Core recv_core_id write 1 to clear the bit send_core_id of the core recv_core_id's COREn_INT_STATUS.
 * \param [in]    send_core_id    the core id which wants to send the inter core interrupt
 * \param [in]    recv_core_id    the core id which will receive the inter core interrupt
 * \remarks
 * - If the ICI ISR has finished the job of send_core_id_n's ICI, then clear bit send_core_id_n;
 *   if it has finished send_core_id_n and send_core_id_m's, then should clear both the bits, etc.
*/
__STATIC_FORCEINLINE void CIDU_ClearInterCoreIntReq(uint32_t send_core_id, uint32_t recv_core_id)
{
    uint32_t val = 0;
    uint32_t* addr = (uint32_t*)CIDU_CORE_INT_STATUS_ADDR(recv_core_id);

    val = (uint32_t)(1UL << send_core_id);
    __SW(addr, val);
}
/** @} */ /* End of Doxygen Group NMSIS_Core_ICI */

/**
 * \defgroup NMSIS_Core_Semaphore      Semaphore Functions
 * \ingroup  NMSIS_Core_CIDU
 * \brief    Functions that configure and use semaphores
 * @{
 * Semaphore is very useful for multi-core cluster without SMP enable.
 *
 * * All Cores in the cluster agree on using SEMAPHORE_n register to protect a critical resource (an UART device for example).
 * * If Core n wants to access the critical resource, it should try to own the SEMPAPHORE_n register, or else it can’t access the critical resource.
 * * When the Core n owns the register SEMPAPHORE_n and finishes the job related the critical resource, then it should
 *   release the register by writing all 1 to it.
 */

/**
 * \brief  Get SEMAPHOREn's value
 * \details
 * Just query the semaphore n's value
 * \param [in]    semph_n     the semaphore id used to protect a critical resource
 * \return register SEMAPHOREn_STATUS value
*/
__STATIC_FORCEINLINE uint32_t CIDU_GetSemaphoreStatus(uint32_t semph_n)
{
    uint32_t val;
    uint32_t* addr = (uint32_t*)CIDU_SEMAPHORE_ADDR(semph_n);

    val = __LW(addr);
    return val;
}

/**
 * \brief  check SEMAPHOREn's acquired status
 * \details
 * Query that whether SEMAPHOREn has been acquired by one core successfully.
 * \param [in]    semph_n    the semaphore id used to protect a critical resource
 * \param [in]    core_id    the core id that wants to access the critical resource
 * \return 0 if core_id has acquired this semaphore successfully, or else -1 if failed
 * \remarks
 * - When the core n owns the register SEMPAPHORE_n and finishes the job related the critical resource,
 *   it should call \ref CIDU_ReleaseSemaphore to release it.
 * \sa
 * - \ref CIDU_GetSemaphoreStatus
 * - \ref CIDU_ReleaseSemaphore
*/
__STATIC_INLINE long CIDU_CheckSemaphoreAcquired(uint32_t semph_n, uint32_t core_id)
{
    uint32_t val;
    val = CIDU_GetSemaphoreStatus(semph_n);
    if (core_id != val) {
        return -1;
    }
    return 0;
}

/**
 * \brief  Acquire the SEMAPHOREn
 * \details
 * Acuqire the SEMAPHOREn, and check the acquired status
 * \param [in]    semph_n    the semaphore id used to protect a critical resource
 * \param [in]    core_id    the core id that wants to access the critical resource
 * \return 0 if core_id has acquired this semaphore successfully, or else -1 if failed
 * \remarks
 * - When the core n owns the register SEMPAPHORE_n and finishes the job related the critical resource,
 *   it should call \ref CIDU_ReleaseSemaphore to release it.
 * \sa
 * - \ref CIDU_CheckSemaphoreAcquired
 * - \ref CIDU_ReleaseSemaphore
*/
__STATIC_INLINE long CIDU_AcquireSemaphore(uint32_t semph_n, uint32_t core_id)
{
    long semaphore_status = -1;
    uint32_t* addr = (uint32_t*)CIDU_SEMAPHORE_ADDR(semph_n);

    __SW(addr, core_id);
    semaphore_status = CIDU_CheckSemaphoreAcquired(semph_n, core_id);
    return semaphore_status;
}

/**
 * \brief  Keep acquiring the SEMAPHOREn until it has acquired this semaphore successfully
 * \details
 * Query that whether SEMAPHOREn has been owned by one core successfully, if not, keep trying.
 * \param [in]    semph_n    the semaphore id used to protect a critical resource
 * \param [in]    core_id    the core id that wants to access the critical resource
 * \remarks
 * - Core n will block here acquiring, so take care that core should release the semaphore when related job done.
 * \sa
 * - \ref CIDU_AcquireSemaphore
 * - \ref CIDU_ReleaseSemaphore
*/
__STATIC_INLINE void CIDU_AcquireSemaphore_Block(uint32_t semph_n, uint32_t core_id)
{
    int32_t semaphore_status = -1;

    while(0 != semaphore_status) {
        semaphore_status = CIDU_AcquireSemaphore(semph_n, core_id);
    }
}

/**
 * \brief  Release the SEMAPHOREn
 * \details
 * Release the SEMAPHOREn by writing all 1 to SEMAPHOREn register.
 * \param [in]    semph_n    the semaphore id used to protect a critical resource
 * \remarks
 * - When the core finishes the job related to the critical resource, it should release the corresponding semaphore.
 * \sa
 * - \ref CIDU_AcquireSemaphore_Block
*/
__STATIC_FORCEINLINE void CIDU_ReleaseSemaphore(uint32_t semph_n)
{
    uint32_t* addr = (uint32_t*)CIDU_SEMAPHORE_ADDR(semph_n);

    /* Release by writing all 1 */
    __SW(addr, 0xFFFFFFFF);
}
/** @} */ /* End of Doxygen Group NMSIS_Core_Semaphore */

/** @} */ /* End of Doxygen Group NMSIS_Core_CIDU_Functions */
#endif /* defined(__CIDU_PRESENT) && (__CIDU_PRESENT == 1) */

#ifdef __cplusplus
}
#endif
#endif /* __CORE_FEATURE_CIDU_H__ */
