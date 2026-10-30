/*!
    \file    gd32vw55x_eclic.c
    \brief   ECLIC(Enhancement Core-Local Interrupt Controller) driver

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

#include "gd32vw55x_eclic.h"
#include "riscv_encoding.h"

/*!
    \brief      enable the global interrupt
    \param[in]  none
    \param[out] none
    \retval     none
*/
void eclic_global_interrupt_enable(void)
{
    __enable_irq();
}

/*!
    \brief      disable the global interrupt
    \param[in]  none
    \param[out] none
    \retval     none
*/
void eclic_global_interrupt_disable(void)
{
    __disable_irq();
}

/*!
    \brief      set machine mode interrupt level threshold
    \param[in]  threshold: the level threshold needed to set (0 ~ 15)
    \param[out] none
    \retval     none
*/
void eclic_level_threshold_set(uint8_t threshold)
{
    ECLIC_SetMth(threshold);
}

/*!
    \brief      set the priority group
    \param[in]  prigroup: specify the priority group
      \arg        ECLIC_PRIGROUP_LEVEL0_PRIO4
      \arg        ECLIC_PRIGROUP_LEVEL1_PRIO3
      \arg        ECLIC_PRIGROUP_LEVEL2_PRIO2
      \arg        ECLIC_PRIGROUP_LEVEL3_PRIO1
      \arg        ECLIC_PRIGROUP_LEVEL4_PRIO0
    \param[out] none
    \retval     none
*/
void eclic_priority_group_set(uint8_t prigroup)
{
    ECLIC_SetCfgNlbits(prigroup);
}

/*!
    \brief      enable the interrupt request
    \param[in]  source: interrupt request, detailed in IRQn_Type
    \param[in]  level: the level needed to set (maximum is 15, refer to the priority group)
    \param[in]  priority: the priority needed to set (maximum is 15, refer to the priority group)
    \param[out] none
    \retval     none
*/
void eclic_irq_enable(IRQn_Type source, uint8_t level, uint8_t priority)
{
    /* level trigger, non-vector mode */
    ECLIC_SetLevelIRQ(source, level);
    ECLIC_SetPriorityIRQ(source, priority);
    ECLIC_EnableIRQ(source);
}

/*!
    \brief      disable the interrupt request
    \param[in]  source: interrupt request, detailed in IRQn_Type
    \param[out] none
    \retval     none
*/
void eclic_irq_disable(IRQn_Type source)
{
    ECLIC_DisableIRQ(source);
}

/*!
    \brief      reset system
    \param[in]  none
    \param[out] none
    \retval     none
*/
void eclic_system_reset(void)
{
    SysTimer_SoftwareReset();
}
