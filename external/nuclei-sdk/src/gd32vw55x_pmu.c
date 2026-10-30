/*!
    \file    gd32vw55x_pmu.c
    \brief   PMU driver

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

#include "gd32vw55x_pmu.h"

/*!
    \brief      reset PMU register
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_deinit(void)
{
    /* reset PMU */
    rcu_periph_reset_enable(RCU_PMURST);
    rcu_periph_reset_disable(RCU_PMURST);
}

/*!
    \brief      select low voltage detector threshold
    \param[in]  lvdt_n:
                only one parameter can be selected which is shown as below:
      \arg        PMU_LVDT_0: voltage threshold is 2.1V
      \arg        PMU_LVDT_1: voltage threshold is 2.3V
      \arg        PMU_LVDT_2: voltage threshold is 2.4V
      \arg        PMU_LVDT_3: voltage threshold is 2.6V
      \arg        PMU_LVDT_4: voltage threshold is 2.7V
      \arg        PMU_LVDT_5: voltage threshold is 2.9V
      \arg        PMU_LVDT_6: voltage threshold is 3.0V
      \arg        PMU_LVDT_7: voltage threshold is 3.1V
    \param[out] none
    \retval     none
*/
void pmu_lvd_select(uint32_t lvdt_n)
{
    /* disable LVD */
    PMU_CTL0 &= ~PMU_CTL0_LVDEN;
    /* clear LVDT bits */
    PMU_CTL0 &= ~PMU_CTL0_LVDT;
    /* set LVDT bits according to lvdt_n */
    PMU_CTL0 |= lvdt_n;
    /* enable LVD */
    PMU_CTL0 |= PMU_CTL0_LVDEN;
}

/*!
    \brief      enable PMU LVD
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_lvd_enable(void)
{
    PMU_CTL0 |= PMU_CTL0_LVDEN;
}

/*!
    \brief      disable PMU LVD
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_lvd_disable(void)
{
    PMU_CTL0 &= ~PMU_CTL0_LVDEN;
}

/*!
    \brief      enable write access to the registers in backup domain
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_backup_write_enable(void)
{
    PMU_CTL0 |= PMU_CTL0_BKPWEN;
}

/*!
    \brief      disable write access to the registers in backup domain
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_backup_write_disable(void)
{
    PMU_CTL0 &= ~PMU_CTL0_BKPWEN;
}


/*!
    \brief      PMU work in sleep mode
    \param[in]  sleepmodecmd:
                only one parameter can be selected which is shown as below:
      \arg        WFI_CMD: use WFI command
      \arg        WFE_CMD: use WFE command
    \param[out] none
    \retval     none
*/
void pmu_to_sleepmode(uint8_t sleepmodecmd)
{
    /* clear sleepdeep bit of RISC-V system control register */
    __set_wfi_sleepmode(WFI_SHALLOW_SLEEP);

    /* select WFI or WFE command to enter sleep mode */
    if(WFI_CMD == sleepmodecmd){
        __WFI();
    }else{
        __disable_irq();
        __WFE();
        __enable_irq();
    }
}

/*!
    \brief      PMU work in deep-sleep mode
    \param[in]  ldo:
                only one parameter can be selected which is shown as below:
      \arg        PMU_LDO_NORMAL: LDO normal work when PMU enter deepsleep mode
      \arg        PMU_LDO_LOWPOWER: LDO work at low power mode when PMU enter deepsleep mode
    \param[in]  lowdrive: 
                only one parameter can be selected which is shown as below:
      \arg        PMU_LOWDRIVER_DISABLE: Low-driver mode disable in deep-sleep mode
      \arg        PMU_LOWDRIVER_ENABLE: Low-driver mode enable in deep-sleep mode
    \param[in]  deepsleepmodecmd:
                only one parameter can be selected which is shown as below:
      \arg        WFI_CMD: use WFI command
      \arg        WFE_CMD: use WFE command
    \param[out] none
    \retval     none
*/
void pmu_to_deepsleepmode(uint32_t ldo, uint32_t lowdrive, uint8_t deepsleepmodecmd)
{
    /* clear stbmod and ldolp bits and low drive bits */
    PMU_CTL0 &= ~((uint32_t)(PMU_CTL0_STBMOD | PMU_CTL0_LDOLP | PMU_CTL0_LDEN | PMU_CTL0_LDNP | PMU_CTL0_LDLP));
    
    /* set ldolp bit according to pmu_ldo */
    PMU_CTL0 |= ldo;
    
    /* low drive mode config in deep-sleep mode */
    if(PMU_LOWDRIVER_ENABLE == lowdrive){
        if(PMU_LDO_NORMAL == ldo){
            PMU_CTL0 |= (uint32_t)(PMU_CTL0_LDEN | PMU_CTL0_LDNP);
        }else{
            PMU_CTL0 |= (uint32_t)(PMU_CTL0_LDEN | PMU_CTL0_LDLP);
        }
    }
    
    /* set CSR_SLEEPVALUE bit of RISC-V system control register */
    __set_wfi_sleepmode(WFI_DEEP_SLEEP);
    
    /* select WFI or WFE command to enter deepsleep mode */
    if(WFI_CMD == deepsleepmodecmd){
        __WFI();
    }else{
        __disable_irq();
        __WFE();
        __enable_irq();
    }    
    /* reset sleepdeep bit of RISC-V system control register */
    __set_wfi_sleepmode(WFI_SHALLOW_SLEEP);
}

/*!
    \brief      PMU work in standby mode
    \param[in]  standbymodecmd:
                only one parameter can be selected which is shown as below:
      \arg        WFI_CMD: use WFI command
      \arg        WFE_CMD: use WFE command
    \param[out] none
    \retval     none
*/
void pmu_to_standbymode(uint8_t standbymodecmd)
{
    /* set CSR_SLEEPVALUE bit of RISC-V system control register */
    __set_wfi_sleepmode(WFI_DEEP_SLEEP);

    /* set stbmod bit */
    PMU_CTL0 |= PMU_CTL0_STBMOD;
        
    /* reset wakeup flag */
    PMU_CTL0 |= PMU_CTL0_WURST;
    
    /* select WFI or WFE command to enter standby mode */
    if(WFI_CMD == standbymodecmd){
        __WFI();
    }else{
        __disable_irq();
        __WFE();
        __enable_irq();
    }
}

/*!
    \brief      enable wakeup pin
    \param[in]  wakeup_pin:
                one or more parameters can be selected which are shown as below:
      \arg        PMU_WAKEUP_PIN0: WKUP Pin 0 (PA0)
      \arg        PMU_WAKEUP_PIN1: WKUP Pin 1 (PA15)
      \arg        PMU_WAKEUP_PIN2: WKUP Pin 2 (PA7)
      \arg        PMU_WAKEUP_PIN3: WKUP Pin 3 (PA12)
    \param[out] none
    \retval     none
*/
void pmu_wakeup_pin_enable(uint32_t wakeup_pin)
{
    PMU_CS0 |= wakeup_pin;
}

/*!
    \brief      disable wakeup pin
    \param[in]  wakeup_pin:
                one or more parameters can be selected which are shown as below:
      \arg        PMU_WAKEUP_PIN0: WKUP Pin 0 (PA0)
      \arg        PMU_WAKEUP_PIN1: WKUP Pin 1 (PA15)
      \arg        PMU_WAKEUP_PIN2: WKUP Pin 2 (PA7)
      \arg        PMU_WAKEUP_PIN3: WKUP Pin 3 (PA12)
    \param[out] none
    \retval     none
*/
void pmu_wakeup_pin_disable(uint32_t wakeup_pin)
{
    PMU_CS0 &= ~(wakeup_pin);
}

/*!
    \brief      enable WIFI power
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_wifi_power_enable(void)
{
    PMU_CTL1 |= PMU_CTL1_WPEN;
}

/*!
    \brief      disable WIFI power
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_wifi_power_disable(void)
{
    PMU_CTL1 &= ~PMU_CTL1_WPEN;
}

/*!
    \brief      WIFI & SRAM low power control
    \param[in]  wifi_sram:
                one or more parameters can be selected which are shown as below:
      \arg        PMU_WIFI_SLEEP: WIFI go to sleep
      \arg        PMU_WIFI_WAKE: WIFI wakeup
      \arg        PMU_SRAM1_SLEEP: SRAM1 go to sleep
      \arg        PMU_SRAM1_WAKE: SRAM1 wakeup
      \arg        PMU_SRAM2_SLEEP: SRAM2 go to sleep
      \arg        PMU_SRAM2_WAKE: SRAM2 wakeup
      \arg        PMU_SRAM3_SLEEP: SRAM3 go to sleep
      \arg        PMU_SRAM3_WAKE: SRAM3 wakeup
      \arg        PMU_SRAM0_SLEEP: SRAM0 go to sleep
      \arg        PMU_SRAM0_WAKE: SRAM0 wakeup
    \param[out] none
    \retval     none
*/
void pmu_wifi_sram_control(uint32_t wifi_sram)
{
    PMU_CTL1 |= wifi_sram;
}

/*!
    \brief      BLE low power control
    \param[in]  ble:
                one or more parameters can be selected which are shown as below:
      \arg        PMU_BLE_SLEEP: BLE go to sleep
      \arg        PMU_BLE_WAKE: BLE wakeup
    \param[out] none
    \retval     none
*/
void pmu_ble_control(uint32_t ble)
{
    PMU_CTL1 |= ble;
}

/*!
    \brief      enable BLE wakeup request
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_ble_wakeup_request_enable(void)
{
    PMU_CTL1 |= PMU_CTL1_BLE_WAKEUP_REQ;
}

/*!
    \brief      disable ble wakeup request
    \param[in]  none
    \param[out] none
    \retval     none
*/
void pmu_ble_wakeup_request_disable(void)
{
    PMU_CTL1 &= ~PMU_CTL1_BLE_WAKEUP_REQ;
}

/*!
    \brief      enable MCU PLL power force open/close
    \param[in]  force:
                only one parameter can be selected which is shown as below:
      \arg        PMU_PLL_FORCE_OPEN: Software force open, open MCU PLL power
      \arg        PMU_PLL_FORCE_CLOSE: Software force close, close MCU PLL power
    \param[out] none
    \retval     none
*/
void pmu_pll_force_enable(uint32_t force)
{
    PMU_RFCTL |= force;
}

/*!
    \brief      disable MCU PLL power open/close force
    \param[in]  force:
                only one parameter can be selected which is shown as below:
      \arg        PMU_PLL_FORCE_OPEN: Software force open, open MCU PLL power
      \arg        PMU_PLL_FORCE_CLOSE: Software force close, close MCU PLL power
    \param[out] none
    \retval     none
*/
void pmu_pll_force_disable(uint32_t force)
{
    PMU_RFCTL &= ~force;
}

/*!
    \brief      configure BLE RF sequence
    \param[in]  mode:
                only one parameter can be selected which is shown as below:
      \arg        PMU_BLE_RF_SOFTWARE: enable RF by software
      \arg        PMU_BLE_RF_HARDWARE: enable RF BLE hardware
    \param[out] none
    \retval     none
*/
void pmu_ble_rf_config(uint32_t mode)
{
    PMU_RFCTL &= ~PMU_RFCTL_BLESWEN;
    PMU_RFCTL |= mode;
}

/*!
    \brief      enable RF sequence force open/close
    \param[in]  force:
                only one parameter can be selected which is shown as below:
      \arg        PMU_RF_FORCE_OPEN: Software force start, open RF power
      \arg        PMU_RF_FORCE_CLOSE: Software force close, close RF power
    \param[out] none
    \retval     none
*/
void pmu_rf_force_enable(uint32_t force)
{
    PMU_RFCTL |= force;
}

/*!
    \brief      disable RF sequence open/close force
    \param[in]  force:
                only one parameter can be selected which is shown as below:
      \arg        PMU_RF_FORCE_OPEN: Software force start, open RF power
      \arg        PMU_RF_FORCE_CLOSE: Software force close, close RF power
    \param[out] none
    \retval     none
*/
void pmu_rf_force_disable(uint32_t force)
{
    PMU_RFCTL &= ~force;
}

/*!
    \brief      configure RF sequence
    \param[in]  mode:
                only one parameter can be selected which is shown as below:
      \arg        PMU_RF_SOFTWARE: RF software sequence enable
      \arg        PMU_RF_HARDWARE: RF hardware sequence enable
    \param[out] none
    \retval     none
*/
void pmu_rf_sequence_config(uint32_t mode)
{
    PMU_RFCTL &= ~PMU_RFCTL_RFSWEN;
    PMU_RFCTL |= mode;
}

/*!
    \brief      get flag state
    \param[in]  flag:
                only one parameter can be selected which is shown as below:
      \arg        PMU_FLAG_WAKEUP: wakeup flag
      \arg        PMU_FLAG_STANDBY: standby flag
      \arg        PMU_FLAG_LVD: VDD low voltage flag
      \arg        PMU_FLAG_LDOVSRF: LDO voltage select ready flag
      \arg        PMU_FLAG_LDRF: low-driver mode ready flag
      \arg        PMU_FLAG_WIFI_SLEEP: WIFI is in sleep state
      \arg        PMU_FLAG_WIFI_ACTIVE: WIFI is in active state
      \arg        PMU_FLAG_BLE_POWER: BLE power status
      \arg        PMU_FLAG_SRAM1_SLEEP: SRAM1 is in sleep state
      \arg        PMU_FLAG_SRAM1_ACTIVE: SRAM1 is in active state
      \arg        PMU_FLAG_SRAM0_SLEEP: SRAM0 is in sleep state
      \arg        PMU_FLAG_SRAM0_ACTIVE: SRAM0 is in active state
      \arg        PMU_FLAG_SRAM2_SLEEP: SRAM2 is in sleep state
      \arg        PMU_FLAG_SRAM2_ACTIVE: SRAM2 is in active state
      \arg        PMU_FLAG_SRAM3_SLEEP: SRAM3 is in sleep state
      \arg        PMU_FLAG_SRAM3_ACTIVE: SRAM3 is in active state
      \arg        PMU_FLAG_BLE_SLEEP: BLE is in sleep state
      \arg        PMU_FLAG_BLE_ACTIVE: BLE is in active state
      \arg        PMU_FLAG_BLE_POWER_FALL: BLE power status falling edge flag
      \arg        PMU_FLAG_BLE_POWER_RISE: BLE power status rising edge flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus pmu_flag_get(uint32_t flag)
{
    if(flag & BIT(31)) {
        flag &= ~BIT(31);
        /* get WIFI SRAM status */
        if(PMU_CS1 & flag) {
            return SET;
        }else {
            return RESET;
        }
    }else if(flag & BIT(30)) {
        flag &= ~BIT(30);
        /* get BLE power status change flag*/
        if(PMU_INTF & flag) {
            return SET;
        }else {
            return RESET;
        }
    }else {
        /* get flag status in PMU_CS0 */
        if(PMU_CS0 & flag) {
            return SET;
        }else {
            return RESET;
        }
    }
}

/*!
    \brief      clear flag bit
    \param[in]  flag:
                only one parameter can be selected which is shown as below:
      \arg        PMU_FLAG_RESET_WAKEUP: reset wakeup flag
      \arg        PMU_FLAG_RESET_STANDBY: reset standby flag
      \arg        PMU_FLAG_RESET_LDRF: reset Low-driver mode ready flag
    \param[out] none
    \retval     none
*/
void pmu_flag_clear(uint32_t flag)
{
    if(PMU_FLAG_RESET_LDRF == flag) {
        PMU_CS0 |= flag;
    }else {
        PMU_CTL0 |= flag;
    }
}

/*!
    \brief      enable PMU interrupt
    \param[in]  interrupt: the PMU interrupt
                only one parameter can be selected which is shown as below:
      \arg        PMU_INT_BLE_POWER_FALL: BLE power status falling edge interrupt
      \arg        PMU_INT_BLE_POWER_RISE: BLE power status rising edge interrupt
    \param[out] none
    \retval     none
*/
void pmu_interrupt_enable(uint32_t interrupt)
{
    PMU_INTEN |= (uint32_t)interrupt;
}

/*!
    \brief      disable PMU interrupt
    \param[in]  interrupt: the PMU interrupt
                only one parameter can be selected which is shown as below:
      \arg        PMU_INT_BLE_POWER_FALL: BLE power status falling edge interrupt
      \arg        PMU_INT_BLE_POWER_RISE: BLE power status rising edge interrupt
    \param[out] none
    \retval     none
*/
void pmu_interrupt_disable(uint32_t interrupt)
{
    PMU_INTEN &= ~((uint32_t)interrupt);
}

/*!
    \brief      get PMU interrupt flag
    \param[in]  int_flag: the PMU interrupt flag
                only one parameter can be selected which is shown as below:
      \arg        PMU_INT_FLAG_BLE_POWER_FALL: BLE power status falling edge interrupt
      \arg        PMU_INT_FLAG_BLE_POWER_RISE: BLE power status rising edge interrupt
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus pmu_interrupt_flag_get(uint32_t int_flag)
{
    FlagStatus interrupt_flag = RESET;
    uint32_t state;
    /* check the interrupt bits */
    switch(int_flag){
    case PMU_INT_FLAG_BLE_POWER_FALL:
        /* get BLE power status rising edge interrupt bits */
        state = PMU_INTF & PMU_INTF_BLE_PS_FALLF;
        if((PMU_INTEN & PMU_INTEN_BLE_PS_FALL_EN) && state){
          interrupt_flag = SET;
        }
        break;
    case PMU_INT_FLAG_BLE_POWER_RISE:
         /* get BLE power status rising edge interrupt bits */
        state = PMU_INTF & PMU_INTF_BLE_PS_RISEF;
          if((PMU_INTEN & PMU_INTEN_BLE_PS_RISE_EN) && state){
            interrupt_flag = SET;
          }
        break;
    default:
        break;
    }
    return interrupt_flag;
}

/*!
    \brief      clear PMU interrupt flag
    \param[in]  int_flag: the PMU interrupt flag
                only one parameter can be selected which is shown as below:
      \arg        PMU_INT_FLAG_RESET_BLE_POWER_FALL: BLE power status falling edge interrupt
      \arg        PMU_INT_FLAG_RESET_BLE_POWER_RISE: BLE power status rising edge interrupt
    \param[out] none
    \retval     none
*/
void pmu_interrupt_flag_clear(uint32_t int_flag)
{
    PMU_INTC |= (uint32_t)int_flag;
}
