/*!
    \file    gd32vw55x_syscfg.c
    \brief   SYSCFG driver

    \version 2023-07-20, V1.0.0, firmware for GD32VW55x
*/

/*
    Copyright (c) 2023, GigaDevice Semiconductor Inc.

    Redistribution and use in source and binary forms, with or without modification, 
are permitted provided that the following conditions are met:

    1. Redistributions of source code must retain the above copyright notice, this 
       list of conditions and the following disclaimer.
    2. Redistributions in binary form must reproduce the above copyright notice, 
       this list of conditions and the following disclaimer in the documentation 
       and/or other materials provided with the distribution.
    3. Neither the name of the copyright holder nor the names of its contributors 
       may be used to endorse or promote products derived from this software without 
       specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED 
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, 
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT 
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR 
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY 
OF SUCH DAMAGE.
*/

#include "gd32vw55x_syscfg.h"

/* SYSCFG_TIMERxCFG bit 0..27 mask */
#define SYSCFG_TIMERCFG_BIT0_27_MASK        0xFFFFFFFU

/*!
    \brief      reset the SYSCFG registers
    \param[in]  none
    \param[out] none
    \retval     none
*/
void syscfg_deinit(void)
{
    rcu_periph_reset_enable(RCU_SYSCFGRST);
    rcu_periph_reset_disable(RCU_SYSCFGRST);
}

/*!
    \brief      configure the GPIO pin as EXTI Line
    \param[in]  exti_port: specify the GPIO port used in EXTI
                only one parameter can be selected which is shown as below:
      \arg          EXTI_SOURCE_GPIOx(x = A,B,C): EXTI GPIO port
    \param[in]  exti_pin: specify the EXTI line
                only one parameter can be selected which is shown as below:
      \arg          EXTI_SOURCE_PINx(GPIOA x = 0..15, GPIOB x = 0..4,11,12,13,15, GPIOC x = 8,13,14,15): EXTI GPIO pin
    \param[out] none
    \retval     none
*/
void syscfg_exti_line_config(uint8_t exti_port, uint8_t exti_pin)
{
    uint32_t clear_exti_mask = ~((uint32_t)EXTI_SS_MASK << (EXTI_SS_MSTEP(exti_pin)));
    uint32_t config_exti_mask = ((uint32_t)exti_port) << (EXTI_SS_MSTEP(exti_pin));

    switch (exti_pin / EXTI_SS_JSTEP){
    case EXTISS0:
        /* clear EXTI source line(0..3) */
        SYSCFG_EXTISS0 &= clear_exti_mask;
        /* configure EXTI source line(0..3) */
        SYSCFG_EXTISS0 |= config_exti_mask;
        break;
    case EXTISS1:
        /* clear EXTI source line(4..7) */
        SYSCFG_EXTISS1 &= clear_exti_mask;
        /* configure EXTI source line(4..7) */
        SYSCFG_EXTISS1 |= config_exti_mask;
        break;
    case EXTISS2:
        /* clear EXTI source line(8..11) */
        SYSCFG_EXTISS2 &= clear_exti_mask;
        /* configure EXTI source line(8..11) */
        SYSCFG_EXTISS2 |= config_exti_mask;
        break;
    case EXTISS3:
        /* clear EXTI source line(12..15) */
        SYSCFG_EXTISS3 &= clear_exti_mask;
        /* configure EXTI source line(12..15) */
        SYSCFG_EXTISS3 |= config_exti_mask;
        break;
    default:
        break;
    }
}

/*!
    \brief      enable I/O compensation cell
    \param[in]  none
    \param[out] none
    \retval     none
*/
void syscfg_io_compensation_enable(void)
{
    SYSCFG_CPSCTL |= SYSCFG_CPSCTL_CPS_EN;
}

/*!
    \brief      disable I/O compensation cell
    \param[in]  none
    \param[out] none
    \retval     none
*/
void syscfg_io_compensation_disable(void)
{
    SYSCFG_CPSCTL &= ~(SYSCFG_CPSCTL_CPS_EN);
}

/*!
    \brief      connect TIMER0/15/16 break input to the selected parameter
    \param[in]  none
    \param[out] none
    \retval     none
*/
void syscfg_lock_config(void)
{
    SYSCFG_CFG1 |= SYSCFG_LOCK_LVD;
}

/*!
    \brief      get the compensation ready flag
    \param[in]  none
    \param[out] none
    \retval     FlagStatus: status of flag (RESET or SET)
*/
FlagStatus syscfg_io_compensation_ready_flag_get(void)
{
    if(RESET != (SYSCFG_CPSCTL & SYSCFG_CPSCTL_CPS_RDY)){
        return SET;
    }
    return RESET;
}

/*!
    \brief      configure the ownership of the shared 32k SRAM
    \param[in]  sram_owner: the ownership of the shared SRAM
                only one parameter can be selected which is shown as below:
      \arg        SRAMEN_WIRELESS: wireless
      \arg        SRAMEN_CORE: core
    \param[out] none
    \retval     none
*/
void syscfg_sram_ownership_config(uint32_t sram_owner)
{
    if(SRAMEN_WIRELESS == sram_owner){
        SYSCFG_SCFG &= ~SYSCFG_SCFG_SOWNSEL;
    }else{
        SYSCFG_SCFG |= SRAMEN_CORE;
    }
}

/*!
    \brief      get code start mode
    \param[in]  none
    \param[out] none
    \retval     syscfg_code_start_enum: code start mode (FLASH_START or SRAM_START or SYSTEM_START)
*/
syscfg_code_start_enum syscfg_boot_mode_get(void)
{
    syscfg_code_start_enum mode;
    if(0x03U == SYSCFG_CFG0){
        mode = SRAM_START;
    }else if(0x01==SYSCFG_CFG0){
        mode = SYSTEM_START;
    }else{
        mode = FLASH_START;
    }
    return mode;
}
