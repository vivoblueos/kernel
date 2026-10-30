/*!
    \file    gd32vw55x_rcu.c
    \brief   RCU driver

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

#include "gd32vw55x_rcu.h"

/* define clock source */
#define SEL_IRC16M                  0x00U                            /* IRC16M is selected as CK_SYS */
#define SEL_HXTAL                   0x01U                            /* HXTAL is selected as CK_SYS */
#define SEL_PLLDIG                  0x02U                            /* PLLDIG is selected as CK_SYS */

/* define startup timeout count */
#define OSC_STARTUP_TIMEOUT         ((uint32_t)0x000FFFFFU)
#define LXTAL_STARTUP_TIMEOUT       ((uint32_t)0x0FFFFFFFU)

/* RCU IRC16M adjust value mask and offset */
#define RCU_IRC16M_ADJUST_MASK      ((uint32_t)0x0000001FU)
#define RCU_IRC16M_ADJUST_OFFSET    ((uint32_t)0x00000003U)

/*!
    \brief      deinitialize the RCU
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_deinit(void)
{
    /* enable IRC16M */
    RCU_CTL |= RCU_CTL_IRC16MEN;
    rcu_osci_stab_wait(RCU_IRC16M);
    RCU_CFG0 &= ~RCU_CFG0_SCS;
    /* reset CFG0 register */
    RCU_CFG0 &= ~(RCU_CFG0_SCS | RCU_CFG0_AHBPSC | RCU_CFG0_APB1PSC | RCU_CFG0_APB2PSC |
                  RCU_CFG0_RTCDIV | RCU_CFG0_CKOUT0SEL  | RCU_CFG0_CKOUT0DIV);
    /* reset CTL register */
    RCU_CTL &= ~(RCU_CTL_HXTALREADY | RCU_CTL_HXTALEN | RCU_CTL_PLLDIGEN |
                 RCU_CTL_HXTALPU | RCU_CTL_PLLDIGPU | RCU_CTL_RFCKMEN);
    /* reset CFG1 register */
    RCU_CFG1 = 0x00000000U;
    /* reset ADDCTL register */
    RCU_ADDCTL = 0x00000000U;
    /* reset PLL register */
    RCU_PLL = 0x00000000U;
    /* reset PLLDIGCFG0 register */
    RCU_PLLDIGCFG0 = 0x00000000U;
    /* reset PLLDIGCFG1 register */
    RCU_PLLDIGCFG1 = 0x00000000U;
    /* reset INT register */
    RCU_INT = 0x00000000U;
}

/*!
    \brief      enable differential signal of IRC16M to RF module
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_irc16m_dfs_to_rf_enable(void)
{
    RCU_CTL |= RCU_CTL_IRC16MRFON;
}

/*!
    \brief      disable differential signal of IRC16M to RF module
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_irc16m_dfs_to_rf_disable(void)
{
    RCU_CTL &= ~RCU_CTL_IRC16MRFON;
}

/*!
    \brief      enable the peripherals clock
    \param[in]  periph: RCU peripherals, refer to rcu_periph_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_GPIOx (x=A,B,C): GPIO ports clock
      \arg        RCU_CRC: CRC clock
      \arg        RCU_WIFI: WIFI clock
      \arg        RCU_WIFIRUN: WIFIRUN clock
      \arg        RCU_SRAMx: (x=0,1,2,3):SRAM clock
      \arg        RCU_DMA: DMA clock
      \arg        RCU_BLE: Blue tooth clock
      \arg        RCU_PKCAU: PKCAU clock
      \arg        RCU_CAU: CAU clock
      \arg        RCU_HAU: HAU clock
      \arg        RCU_TRNG: TRNG clock
      \arg        RCU_QSPI: QSPI clock
      \arg        RCU_TIMERx (x=0,1,2,5,15,16): TIMER clock
      \arg        RCU_WWDGT: WWDGT clock
      \arg        RCU_SPI: SPI clock
      \arg        RFI: RFI clock
      \arg        RCU_USART0: USART clock
      \arg        RCU_UARTx (x=1,2): UART clock
      \arg        RCU_I2Cx (x=0,1): I2C clock
      \arg        RCU_PMU: PMU clock
      \arg        RCU_RTC: RTC clock
      \arg        RCU_ADC : ADC clock
      \arg        RCU_SYSCFG: SYSCFG clock
      \arg        RCU_RF: RF clock
    \param[out] none
    \retval     none
*/
void rcu_periph_clock_enable(rcu_periph_enum periph)
{
    RCU_REG_VAL(periph) |= BIT(RCU_BIT_POS(periph));
}

/*!
    \brief      disable the peripherals clock
    \param[in]  periph: RCU peripherals, refer to rcu_periph_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_GPIOx (x=A,B,C): GPIO ports clock
      \arg        RCU_CRC: CRC clock
      \arg        RCU_WIFI: WIFI clock
      \arg        RCU_WIFIRUN: WIFIRUN clock
      \arg        RCU_SRAMx: (x=0,1,2):SRAM clock
      \arg        RCU_DMA: DMA clock
      \arg        RCU_BLE: Blue tooth clock
      \arg        RCU_PKCAU: PKCAU clock
      \arg        RCU_CAU: CAU clock
      \arg        RCU_HAU: HAU clock
      \arg        RCU_TRNG: TRNG clock
      \arg        RCU_QSPI: QSPI clock
      \arg        RCU_TIMERx (x=0,1,2,5,15,16): TIMER clock
      \arg        RCU_WWDGT: WWDGT clock
      \arg        RCU_SPI: SPI clock
      \arg        RFI: RFI clock
      \arg        RCU_USART0 : USART clock
      \arg        RCU_UARTx (x=1,2): UART clock
      \arg        RCU_I2Cx (x=0,1): I2C clock
      \arg        RCU_PMU: PMU clock
      \arg        RCU_RTC: RTC clock
      \arg        RCU_ADC: ADC clock
      \arg        RCU_SYSCFG: SYSCFG clock
      \arg        RCU_RF: RF clock
    \param[out] none
    \retval     none
*/
void rcu_periph_clock_disable(rcu_periph_enum periph)
{
    RCU_REG_VAL(periph) &= ~BIT(RCU_BIT_POS(periph));
}

/*!
    \brief      enabled FMC clock when sleep mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_fmc_clock_sleep_enable(void)
{
    RCU_AHB1SPEN |= RCU_AHB1SPEN_FMCSPEN;
}

/*!
    \brief      disabled FMC clock when sleep mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_fmc_clock_sleep_disable(void)
{
    RCU_AHB1SPEN &= ~RCU_AHB1SPEN_FMCSPEN;
}

/*!
    \brief      reset the peripherals
    \param[in]  periph_reset: RCU peripherals reset, refer to rcu_periph_reset_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_GPIOxRST (x=A,B,C): reset GPIO ports
      \arg        RCU_CRCRST: reset CRC
      \arg        RCU_WIFIRST: reset WIFI
      \arg        RCU_DMARST: reset DMA
      \arg        RCU_BLERST:reset Blue tooth
      \arg        RCU_PKCAURST: reset PKCAU
      \arg        RCU_CAURST: reset CAU
      \arg        RCU_HAURST: reset HAU
      \arg        RCU_TRNGRST: reset TRNG
      \arg        RCU_QSPIRST: reset QSPI
      \arg        RCU_TIMERxRST (x=0,1,2,5,15,16): reset TIMER
      \arg        RCU_WWDGTRST: reset WWDGT
      \arg        RCU_SPIRST: reset SPI
      \arg        RCU_RFIRST: reset RFI
      \arg        RCU_USART0RST : reset USART
      \arg        RCU_UARTxRST (x=1,2): reset UART
      \arg        RCU_I2CxRST (x=0,1): reset I2C
      \arg        RCU_PMURST: reset PMU
      \arg        RCU_ADCRST : reset ADC
      \arg        RCU_SYSCFGRST: reset SYSCFG
      \arg        RCU_RFRST: reset RF
    \param[out] none
    \retval     none
*/
void rcu_periph_reset_enable(rcu_periph_reset_enum periph_reset)
{
    RCU_REG_VAL(periph_reset) |= BIT(RCU_BIT_POS(periph_reset));
}

/*!
    \brief      disable reset the peripheral
    \param[in]  periph_reset: RCU peripherals reset, refer to rcu_periph_reset_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_GPIOxRST (x=A,B,C): reset GPIO ports
      \arg        RCU_CRCRST: reset CRC
      \arg        RCU_WIFIRST: reset WIFI
      \arg        RCU_DMARST: reset DMA
      \arg        RCU_BLERST:reset Blue tooth
      \arg        RCU_PKCAURST: reset PKCAU
      \arg        RCU_CAURST: reset CAU
      \arg        RCU_HAURST: reset HAU
      \arg        RCU_TRNGRST: reset TRNG
      \arg        RCU_QSPIRST: reset QSPI
      \arg        RCU_TIMERxRST (x=0,1,2,5,15,16): reset TIMER
      \arg        RCU_WWDGTRST: reset WWDGT
      \arg        RCU_SPIRST: reset SPI
      \arg        RCU_RFIRST: reset RFI
      \arg        RCU_USART0RST: reset USART
      \arg        RCU_UARTxRST (x=1,2): reset UART
      \arg        RCU_I2CxRST (x=0,1): reset I2C
      \arg        RCU_PMURST: reset PMU
      \arg        RCU_ADCRST : reset ADC
      \arg        RCU_SYSCFGRST: reset SYSCFG
      \arg        RCU_RFRST: reset RF
    \param[out] none
    \retval     none
*/
void rcu_periph_reset_disable(rcu_periph_reset_enum periph_reset)
{
    RCU_REG_VAL(periph_reset) &= ~BIT(RCU_BIT_POS(periph_reset));
}

/*!
    \brief      reset the BKP
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_bkp_reset_enable(void)
{
    RCU_BDCTL |= RCU_BDCTL_BKPRST;
}

/*!
    \brief      disable the BKP reset
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_bkp_reset_disable(void)
{
    RCU_BDCTL &= ~RCU_BDCTL_BKPRST;
}

/*!
    \brief      enable the RF PLL calculation
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_rfpll_cal_enable(void)
{
    RCU_CFG1 |= RCU_CFG1_RFPLLCALEN;
}

/*!
    \brief      disable the RF PLL calculation
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_rfpll_cal_disable(void)
{
    RCU_CFG1 &= ~RCU_CFG1_RFPLLCALEN;
}

/*!
    \brief      power up rcu control unit
    \param[in]  rcu_unit: rcu power up control unit select
                only one parameter can be selected which is shown as below:
      \arg        RCU_UNIT_HXTAL: HXTAL
      \arg        RCU_UNIT_PLLDIG: PLLDIG 
      \arg        RCU_UNIT_RFPLL: RFPLL
      \arg        RCU_UNIT_LDOANA: LDOANA
      \arg        RCU_UNIT_LDOCLK: LDOCLK
      \arg        RCU_UNIT_BANDGAP: BANDGAP
    \param[out] none
    \retval     none
*/
void rcu_control_unit_powerup(rcu_unit_enum rcu_unit)
{
    RCU_REG_VAL(rcu_unit) |= BIT(RCU_BIT_POS(rcu_unit));
}

/*!
    \brief      power down rcu control unit
    \param[in]  rcu_unit: rcu power down control unit select
                only one parameter can be selected which is shown as below:
      \arg        RCU_UNIT_HXTAL: HXTAL
      \arg        RCU_UNIT_PLLDIG: PLLDIG
      \arg        RCU_UNIT_RFPLL: RFPLL
      \arg        RCU_UNIT_LDOANA: LDOANA
      \arg        RCU_UNIT_LDOCLK: LDOCLK
      \arg        RCU_UNIT_BANDGAP: BANDGAP
    \param[out] none
    \retval     none
*/
void rcu_control_unit_powerdown(rcu_unit_enum rcu_unit)
{
    RCU_REG_VAL(rcu_unit) &= ~BIT(RCU_BIT_POS(rcu_unit));
}

/*!
    \brief      configure the system clock source
    \param[in]  ck_sys: system clock source select
                only one parameter can be selected which is shown as below:
      \arg        RCU_CKSYSSRC_IRC16M: select CK_IRC16M as the CK_SYS source
      \arg        RCU_CKSYSSRC_HXTAL: select CK_HXTAL as the CK_SYS source
      \arg        RCU_CKSYSSRC_PLLDIG: select CK_PLLDIG as the CK_SYS source
    \param[out] none
    \retval     none
*/
void rcu_system_clock_source_config(uint32_t ck_sys)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the SCS bits and set according to ck_sys */
    reg &= ~RCU_CFG0_SCS;
    RCU_CFG0 = (reg | ck_sys);
}

/*!
    \brief      get the system clock source
    \param[in]  none
    \param[out] none
    \retval     which clock is selected as CK_SYS source
      \arg        RCU_SCSS_IRC16M: CK_IRC16M is selected as the CK_SYS source
      \arg        RCU_SCSS_HXTAL: CK_HXTAL is selected as the CK_SYS source
      \arg        RCU_CKSYSSRC_PLLDIG: CK_PLLDIG is selected as the CK_SYS source
*/
uint32_t rcu_system_clock_source_get(void)
{
    return (RCU_CFG0 & RCU_CFG0_SCSS);
}

/*!
    \brief      configure the AHB clock prescaler selection
    \param[in]  ck_ahb: AHB clock prescaler selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_AHB_CKSYS_DIVx, x=1, 2, 4, 8, 16, 64, 128, 256, 512
    \param[out] none
    \retval     none
*/
void rcu_ahb_clock_config(uint32_t ck_ahb)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the AHBPSC bits and set according to ck_ahb */
    reg &= ~RCU_CFG0_AHBPSC;
    RCU_CFG0 = (reg | ck_ahb);
}

/*!
    \brief      configure the APB1 clock prescaler selection
    \param[in]  ck_apb1: APB1 clock prescaler selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_APB1_CKAHB_DIV1: select CK_AHB as CK_APB1
      \arg        RCU_APB1_CKAHB_DIV2: select CK_AHB/2 as CK_APB1
      \arg        RCU_APB1_CKAHB_DIV4: select CK_AHB/4 as CK_APB1
      \arg        RCU_APB1_CKAHB_DIV8: select CK_AHB/8 as CK_APB1
      \arg        RCU_APB1_CKAHB_DIV16: select CK_AHB/16 as CK_APB1
    \param[out] none
    \retval     none
*/
void rcu_apb1_clock_config(uint32_t ck_apb1)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the APB1PSC and set according to ck_apb1 */
    reg &= ~RCU_CFG0_APB1PSC;
    RCU_CFG0 = (reg | ck_apb1);
}

/*!
    \brief      configure the APB2 clock prescaler selection
    \param[in]  ck_apb2: APB2 clock prescaler selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_APB2_CKAHB_DIV1: select CK_AHB as CK_APB2
      \arg        RCU_APB2_CKAHB_DIV2: select CK_AHB/2 as CK_APB2
      \arg        RCU_APB2_CKAHB_DIV4: select CK_AHB/4 as CK_APB2
      \arg        RCU_APB2_CKAHB_DIV8: select CK_AHB/8 as CK_APB2
      \arg        RCU_APB2_CKAHB_DIV16: select CK_AHB/16 as CK_APB2
    \param[out] none
    \retval     none
*/
void rcu_apb2_clock_config(uint32_t ck_apb2)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the APB2PSC and set according to ck_apb2 */
    reg &= ~RCU_CFG0_APB2PSC;
    RCU_CFG0 = (reg | ck_apb2);
}

/*!
    \brief      configure the CK_OUT0 clock source and divider
    \param[in]  ckout0_src: CK_OUT0 clock source selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_CKOUT0SRC_IRC16M: IRC16M selected
      \arg        RCU_CKOUT0SRC_LXTAL: LXTAL selected
      \arg        RCU_CKOUT0SRC_HXTAL: HXTAL selected
      \arg        RCU_CKOUT0SRC_PLLDIG: CK_PLLDIG selected
      \arg        RCU_CKOUT0SRC_IRC32K: IRC32K selected
      \arg        RCU_CKOUT0SRC_CKSYS: system clock selected
    \param[in]  ckout0_div: CK_OUT0 divider 
      \arg        RCU_CKOUT0_DIVx(x=1,2,3,4,5): CK_OUT0 is divided by x
    \param[out] none
    \retval     none
*/
void rcu_ckout0_config(uint32_t ckout0_src, uint32_t ckout0_div)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the CKOUT0SRC, CKOUT0DIV and set according to ckout0_src and ckout0_div */
    reg &= ~(RCU_CFG0_CKOUT0SEL | RCU_CFG0_CKOUT0DIV );
    RCU_CFG0 = (reg | ckout0_src | ckout0_div);
}

/*!
    \brief      configure the CK_OUT1 clock source and divider
    \param[in]  ckout1_src: CK_OUT1 clock source selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_CKOUT1SRC_CKSYS: system clock selected
      \arg        RCU_CKOUT1SRC_IRC16M: IRC16M selected
      \arg        RCU_CKOUT1SRC_HXTAL: HXTAL selected
      \arg        RCU_CKOUT1SRC_PLLDIG: PLLDIG selected           
    \param[in]  ckout1_div: CK_OUT1 divider 
      \arg        RCU_CKOUT1_DIVx(x=1,2,3,4,5): CK_OUT1 is divided by x
    \param[out] none
    \retval     none
*/
void rcu_ckout1_config(uint32_t ckout1_src, uint32_t ckout1_div)
{
    uint32_t reg;
    
    reg = RCU_CFG0;
    /* reset the CKOUT1SRC, CKOUT1DIV and set according to ckout1_src and ckout1_div */
    reg &= ~(RCU_CFG0_CKOUT1SEL | RCU_CFG0_CKOUT1DIV);
    RCU_CFG0 = (reg | ckout1_src | ckout1_div);
}

/*!
    \brief      configure the PLLDIG output clock frequency
    \param[in]  plldig_clk: the PLLDIG VCO clock this parameter sselection
                only one parameter can be selected which is shown as below:
      \arg        RCU_PLLDIG_192M: selected 192Mhz as PLLDIG output frequency
      \arg        RCU_PLLDIG_240M: selected 240Mhz as PLLDIG output frequency
      \arg        RCU_PLLDIG_320M: selected 320Mhz as PLLDIG output frequency
      \arg        RCU_PLLDIG_480M: selected 480Mhz as PLLDIG output frequency
    \param[out] none
    \retval     none
*/
void rcu_plldig_config(uint32_t plldig_clk)
{
       RCU_PLLDIGCFG0 &= ~(RCU_PLLDIGCFG0_PLLDIGOSEL);
       RCU_PLLDIGCFG0 |= plldig_clk;
}

/*!
    \brief      configure PLLDIG clock divider factor for system clock
    \param[in]  plldigdiv_sys: PLLDIG clock divider factor for system clock
                only one parameter can be selected which is shown as below:
      \arg        RCU_PLLDIG_SYS_DIVx(x=1,2,3,...,64): PLLDIG clock divided by x for system clock
    \param[out] none
    \retval     none
*/
void rcu_plldigdiv_sys_config(uint32_t plldigdiv_sys)
{
    uint32_t reg;

    reg = RCU_PLLDIGCFG0;
    /* reset the PLLDIGDIV_SYS bits and set according to plldigdiv_sys */
    reg &= ~RCU_PLLDIGCFG0_PLLDIGDIV_SYS;
    RCU_PLLDIGCFG0 = (reg | plldigdiv_sys);
}

/*!
    \brief      configure the RTC clock source selection
    \param[in]  rtc_clock_source: RTC clock source selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_RTCSRC_NONE: no clock selected
      \arg        RCU_RTCSRC_LXTAL: CK_LXTAL selected as RTC source clock
      \arg        RCU_RTCSRC_IRC32K: CK_IRC32K selected as RTC source clock
      \arg        RCU_RTCSRC_HXTAL_DIV_RTCDIV: CK_HXTAL/RTCDIV selected as RTC source clock
    \param[out] none
    \retval     none
*/
void rcu_rtc_clock_config(uint32_t rtc_clock_source)
{
    uint32_t reg;
    
    reg = RCU_BDCTL; 
    /* reset the RTCSRC bits and set according to rtc_clock_source */
    reg &= ~RCU_BDCTL_RTCSRC;
    RCU_BDCTL = (reg | rtc_clock_source);
}

/*!
    \brief      configure the frequency division of RTC clock when HXTAL was selected as its clock source 
    \param[in]  rtc_div: RTC clock frequency division
                only one parameter can be selected which is shown as below:
      \arg        RCU_RTC_HXTAL_DIVx: RTCDIV clock select CK_HXTAL/x, x = 1 2....31
    \param[out] none
    \retval     none
*/
void rcu_rtc_div_config(uint32_t rtc_div)
{
    uint32_t reg;    
    reg = RCU_CFG0; 
    /* reset the RTCDIV bits and set according to rtc_div value */
    reg &= ~RCU_CFG0_RTCDIV;
    RCU_CFG0 = (reg | rtc_div);
}

/*!
    \brief      configure the frequency division of the TRNG source clock
    \param[in]  trng_div: TRNG clock frequency division
                only one parameter can be selected which is shown as below:
      \arg        RCU_TRNG_DIVx: TRNG clock select x, x = 1....32
    \param[out] none
    \retval     none
*/
void rcu_trng_div_config(uint32_t trng_div)
{
    uint32_t reg;
    reg = RCU_ADDCTL;
    /* reset the TRNGCKDIV bits and set according to trng_div value */
    reg &= ~RCU_ADDCTL_TRNGCKDIV;
    RCU_ADDCTL = (reg | trng_div);
}

/*!
    \brief      configure the I2C0 clock source selection
    \param[in]  i2c0_clock_source: I2C0 clock source selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_I2C0SRC_CKAPB1: CK_APB1 selected as I2C0 source clock
      \arg        RCU_I2C0SRC_CKSYS: CK_SYS selected as I2C0 source clock
      \arg        RCU_I2C0SRC_IRC16M: CK_IRC16M selected as I2C0 source clock
    \param[out] none
    \retval     none
*/
void rcu_i2c0_clock_config(uint32_t i2c0_clock_source)
{
    uint32_t reg;
    
    reg = RCU_CFG1; 
    /* reset the I2C0SEL bit and set according to i2c0_clock_source */
    reg &= ~RCU_CFG1_I2C0SEL;
    RCU_CFG1 = (reg | i2c0_clock_source);
}

/*!
    \brief      configure the USART0 clock source selection
    \param[in]  usart0_clock_source: USART0 clock source selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_USART0SRC_CKAPB1: CK_APB1 selected as USART0 source clock
      \arg        RCU_USART0SRC_CKSYS: CK_SYS selected as USART0 source clock
      \arg        RCU_USART0SRC_LXTAL: CK_LXTAL selected as USART0 source clock
      \arg        RCU_USART0SRC_IRC16M: CK_IRC16M selected as USART0 source clock
    \param[out] none
    \retval     none
*/
void rcu_usart0_clock_config(uint32_t usart0_clock_source)
{
    uint32_t reg;
    
    reg = RCU_CFG1; 
    /* reset the USART0SEL bit and set according to usart0_clock_source */
    reg &= ~RCU_CFG1_USART0SEL;
    RCU_CFG1 = (reg | usart0_clock_source);
}

/* configure IRC16M clock divider factor for system clock */
/*!
    \brief      configure IRC16M clock divider factor for system clock
    \param[in]  irc16m_div: IRC16M clock divider factor for system clock
                only one parameter can be selected which is shown as below:
      \arg        RCU_IRC16M_DIVx(x=1,2,3,...,512): IRC16M clock divided by x for system clock
    \param[out] none
    \retval     none
*/
void rcu_irc16m_div_config(uint32_t irc16m_div)
{
    uint32_t reg;
    reg = RCU_CFG1;
    /* reset the IRC16MDIV bits and set according to irc16m_div */
    reg &= ~RCU_CFG1_IRC16MDIV;
    RCU_CFG1 = (reg | irc16m_div);
}

/*!
    \brief      configure the TIMER clock prescaler selection
    \param[in]  timer_clock_prescaler: TIMER clock selection
                only one parameter can be selected which is shown as below:
      \arg        RCU_TIMER_PSC_MUL2: if APB1PSC/APB2PSC in RCU_CFG0 register is 0b0xx(CK_APBx = CK_AHB) 
                                      or 0b100(CK_APBx = CK_AHB/2), the TIMER clock is equal to CK_AHB(CK_TIMERx = CK_AHB).
                                      or else, the TIMER clock is twice the corresponding APB clock (TIMER in APB1 domain: CK_TIMERx = 2 x CK_APB1; 
                                      TIMER in APB2 domain: CK_TIMERx = 2 x CK_APB2)
      \arg        RCU_TIMER_PSC_MUL4: if APB1PSC/APB2PSC in RCU_CFG0 register is 0b0xx(CK_APBx = CK_AHB), 
                                      0b100(CK_APBx = CK_AHB/2), or 0b101(CK_APBx = CK_AHB/4), the TIMER clock is equal to CK_AHB(CK_TIMERx = CK_AHB). 
                                      or else, the TIMER clock is four timers the corresponding APB clock (TIMER in APB1 domain: CK_TIMERx = 4 x CK_APB1;  
                                      TIMER in APB2 domain: CK_TIMERx = 4 x CK_APB2)
    \param[out] none
    \retval     none
*/
void rcu_timer_clock_prescaler_config(uint32_t timer_clock_prescaler)
{
    /* configure the TIMERSEL bit and select the TIMER clock prescaler */
    if(timer_clock_prescaler == RCU_TIMER_PSC_MUL2){
        RCU_CFG1 &= timer_clock_prescaler;
    }else{
        RCU_CFG1 |= timer_clock_prescaler;
    }
}

/*!
    \brief      get the clock stabilization and periphral reset flags
    \param[in]  flag: the clock stabilization and periphral reset flags, refer to rcu_flag_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_FLAG_IRC16MSTB: IRC16M stabilization flag
      \arg        RCU_FLAG_HXTALSTB: HXTAL stabilization flag
      \arg        RCU_FLAG_PLLDIGSTB: PLLDIG stabilization flag
      \arg        RCU_FLAG_LXTALSTB: LXTAL stabilization flag
      \arg        RCU_FLAG_IRC32KSTB: IRC32K stabilization flag
      \arg        RCU_FLAG_EPRST: external PIN reset flag
      \arg        RCU_FLAG_PORRST: power reset flag
      \arg        RCU_FLAG_SWRST: software reset flag
      \arg        RCU_FLAG_FWDGTRST: free watchdog timer reset flag
      \arg        RCU_FLAG_WWDGTRST: window watchdog timer reset flag
      \arg        RCU_FLAG_LPRST: low-power reset flag
    \param[out] none
    \retval     none
*/
FlagStatus rcu_flag_get(rcu_flag_enum flag)
{
    /* get the rcu flag */
    if(RESET != (RCU_REG_VAL(flag) & BIT(RCU_BIT_POS(flag)))){
        return SET;
    }else{
        return RESET;
    }
}

/*!
    \brief      clear all the reset flag
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_all_reset_flag_clear(void)
{
    RCU_RSTSCK |= RCU_RSTSCK_RSTFC;
}

/*!
    \brief      get the clock stabilization interrupt and ckm flags
    \param[in]  int_flag: interrupt and ckm flags, refer to rcu_int_flag_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_INT_FLAG_IRC32KSTB: IRC32K stabilization interrupt flag
      \arg        RCU_INT_FLAG_LXTALSTB: LXTAL stabilization interrupt flag
      \arg        RCU_INT_FLAG_IRC16MSTB: IRC16M stabilization interrupt flag
      \arg        RCU_INT_FLAG_HXTALSTB: HXTAL stabilization interrupt flag
      \arg        RCU_INT_FLAG_PLLDIGSTB: PLLDIG stabilization interrupt flag
      \arg        RCU_INT_FLAG_CKM: HXTAL clock stuck interrupt flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus rcu_interrupt_flag_get(rcu_int_flag_enum int_flag)
{
    /* get the rcu interrupt flag */
    if(RESET != (RCU_REG_VAL(int_flag) & BIT(RCU_BIT_POS(int_flag)))){
        return SET;
    }else{
        return RESET;
    }
}

/*!
    \brief      clear the interrupt flags
    \param[in]  int_flag: clock stabilization and stuck interrupt flags clear, refer to rcu_int_flag_clear_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_INT_FLAG_IRC32KSTB_CLR: IRC32K stabilization interrupt flag clear
      \arg        RCU_INT_FLAG_LXTALSTB_CLR: LXTAL stabilization interrupt flag clear
      \arg        RCU_INT_FLAG_IRC16MSTB_CLR: IRC16M stabilization interrupt flag clear
      \arg        RCU_INT_FLAG_HXTALSTB_CLR: HXTAL stabilization interrupt flag clear
      \arg        RCU_INT_FLAG_PLLDIGSTB_CLR: PLLDIG stabilization interrupt flag clear
      \arg        RCU_INT_FLAG_CKM_CLR: clock stuck interrupt flag clear
    \param[out] none
    \retval     none
*/
void rcu_interrupt_flag_clear(rcu_int_flag_clear_enum int_flag)
{
    RCU_REG_VAL(int_flag) |= BIT(RCU_BIT_POS(int_flag));
}

/*!
    \brief      enable the stabilization interrupt
    \param[in]  interrupt: clock stabilization interrupt, refer to rcu_int_enum
                Only one parameter can be selected which is shown as below:
      \arg        RCU_INT_IRC32KSTB: IRC32K stabilization interrupt enable
      \arg        RCU_INT_LXTALSTB: LXTAL stabilization interrupt enable
      \arg        RCU_INT_IRC16MSTB: IRC16M stabilization interrupt enable
      \arg        RCU_INT_HXTALSTB: HXTAL stabilization interrupt enable
      \arg        RCU_INT_PLLDIGSTB: PLLDIG stabilization interrupt enable
    \param[out] none
    \retval     none
*/
void rcu_interrupt_enable(rcu_int_enum interrupt)
{
    RCU_REG_VAL(interrupt) |= BIT(RCU_BIT_POS(interrupt));
}

/*!
    \brief      disable the stabilization interrupt
    \param[in]  interrupt: clock stabilization interrupt, refer to rcu_int_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_INT_IRC32KSTB: IRC32K stabilization interrupt disable
      \arg        RCU_INT_LXTALSTB: LXTAL stabilization interrupt disable
      \arg        RCU_INT_IRC16MSTB: IRC16M stabilization interrupt disable
      \arg        RCU_INT_HXTALSTB: HXTAL stabilization interrupt disable
      \arg        RCU_INT_PLLDIGSTB: PLLDIG stabilization interrupt disable
    \param[out] none
    \retval     none
*/
void rcu_interrupt_disable(rcu_int_enum interrupt)
{
    RCU_REG_VAL(interrupt) &= ~BIT(RCU_BIT_POS(interrupt));
}

/*!
    \brief      configure the LXTAL drive capability
    \param[in]  lxtal_dricap: drive capability of LXTAL
                only one parameter can be selected which is shown as below:
      \arg        RCU_LXTALDRI_LOWER_DRIVE: lower driving capability
      \arg        RCU_LXTALDRI_HIGH_DRIVE: high driving capability
      \arg        RCU_LXTALDRI_HIGHER_DRIVE: higher driving capability
      \arg        RCU_LXTALDRI_HIGHEST_DRIVE: highest driving capability
    \param[out] none
    \retval     none
*/
void rcu_lxtal_drive_capability_config(uint32_t lxtal_dricap)
{
    uint32_t reg;
    
    reg = RCU_BDCTL;
    
    /* reset the LXTALDRI bits and set according to lxtal_dricap */
    reg &= ~RCU_BDCTL_LXTALDRI;
    RCU_BDCTL = (reg | lxtal_dricap);
}

/*!
    \brief      wait for oscillator stabilization flags is SET or oscillator startup is timeout
    \param[in]  osci: oscillator types, refer to rcu_osci_type_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_HXTAL: HXTAL
      \arg        RCU_LXTAL: LXTAL
      \arg        RCU_IRC16M: IRC16M
      \arg        RCU_IRC32K: IRC32K
      \arg        RCU_PLLDIG_CK: PLLDIG
    \param[out] none
    \retval     ErrStatus: SUCCESS or ERROR
*/
ErrStatus rcu_osci_stab_wait(rcu_osci_type_enum osci)
{
    uint32_t stb_cnt = 0U;
    ErrStatus reval = ERROR;
    FlagStatus osci_stat = RESET;
    
    switch(osci){
    /* wait HXTAL stable */
    case RCU_HXTAL:
        while((RESET == osci_stat) && (HXTAL_STARTUP_TIMEOUT != stb_cnt)){
            osci_stat = rcu_flag_get(RCU_FLAG_HXTALSTB);
            stb_cnt++;
        }
        
        /* check whether flag is set */
        if(RESET != rcu_flag_get(RCU_FLAG_HXTALSTB)){
            reval = SUCCESS;
        }
        break;
    /* wait LXTAL stable */
    case RCU_LXTAL:
        while((RESET == osci_stat) && (LXTAL_STARTUP_TIMEOUT != stb_cnt)){
            osci_stat = rcu_flag_get(RCU_FLAG_LXTALSTB);
            stb_cnt++;
        }
        
        /* check whether flag is set */
        if(RESET != rcu_flag_get(RCU_FLAG_LXTALSTB)){
            reval = SUCCESS;
        }
        break;
    /* wait IRC16M stable */    
    case RCU_IRC16M:
        while((RESET == osci_stat) && (IRC16M_STARTUP_TIMEOUT != stb_cnt)){
            osci_stat = rcu_flag_get(RCU_FLAG_IRC16MSTB);
            stb_cnt++;
        }
        
        /* check whether flag is set */
        if(RESET != rcu_flag_get(RCU_FLAG_IRC16MSTB)){
            reval = SUCCESS;
        }
        break;
    /* wait IRC32K stable */
    case RCU_IRC32K:
        while((RESET == osci_stat) && (OSC_STARTUP_TIMEOUT != stb_cnt)){
            osci_stat = rcu_flag_get(RCU_FLAG_IRC32KSTB);
            stb_cnt++;
        }
        
        /* check whether flag is set */
        if(RESET != rcu_flag_get(RCU_FLAG_IRC32KSTB)){
            reval = SUCCESS;
        }
        break;
    /* wait PLLDIG stable */    
    case RCU_PLLDIG_CK:
        while((RESET == osci_stat) && (OSC_STARTUP_TIMEOUT != stb_cnt)){
            osci_stat = rcu_flag_get(RCU_FLAG_PLLDIGSTB);
            stb_cnt++;
        }
        
        /* check whether flag is set */
        if(RESET != rcu_flag_get(RCU_FLAG_PLLDIGSTB)){
            reval = SUCCESS;
        }
        break;
    default:
        break;
    }
    
    /* return value */
    return reval;
}

/*!
    \brief      turn on the oscillator
    \param[in]  osci: oscillator types, refer to rcu_osci_type_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_HXTAL: HXTAL
      \arg        RCU_LXTAL: LXTAL
      \arg        RCU_IRC16M: IRC16M
      \arg        RCU_IRC32K: IRC32K
      \arg        RCU_PLLDIG_CK: PLLDIG
    \param[out] none
    \retval     none
*/
void rcu_osci_on(rcu_osci_type_enum osci)
{
    RCU_REG_VAL(osci) |= BIT(RCU_BIT_POS(osci));
}

/*!
    \brief      turn off the oscillator
    \param[in]  osci: oscillator types, refer to rcu_osci_type_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_HXTAL: HXTAL
      \arg        RCU_LXTAL: LXTAL
      \arg        RCU_IRC16M: IRC16M
      \arg        RCU_IRC32K: IRC32K
      \arg        RCU_PLLDIG_CK: PLLDIG
    \param[out] none
    \retval     none
*/
void rcu_osci_off(rcu_osci_type_enum osci)
{
    RCU_REG_VAL(osci) &= ~BIT(RCU_BIT_POS(osci));
}

/*!
    \brief      enable the oscillator bypass mode, HXTALEN or LXTALEN must be reset before it
    \param[in]  osci: oscillator types, refer to rcu_osci_type_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_HXTAL: high speed crystal oscillator(HXTAL)
      \arg        RCU_LXTAL: low speed crystal oscillator(LXTAL)
    \param[out] none
    \retval     none
*/
void rcu_osci_bypass_mode_enable(rcu_osci_type_enum osci)
{
    uint32_t reg;

    switch(osci){
    /* enable HXTAL to bypass mode */    
    case RCU_HXTAL:
        reg = RCU_CTL;
        RCU_CTL &= ~RCU_CTL_HXTALEN;
        RCU_CTL = (reg | RCU_CTL_HXTALBPS);
        break;
    /* enable LXTAL to bypass mode */
    case RCU_LXTAL:
        reg = RCU_BDCTL;
        RCU_BDCTL &= ~RCU_BDCTL_LXTALEN;
        RCU_BDCTL = (reg | RCU_BDCTL_LXTALBPS);
        break;
    default:
        break;
    }
}

/*!
    \brief      disable the oscillator bypass mode, HXTALEN or LXTALEN must be reset before it
    \param[in]  osci: oscillator types, refer to rcu_osci_type_enum
                only one parameter can be selected which is shown as below:
      \arg        RCU_HXTAL: high speed crystal oscillator(HXTAL)
      \arg        RCU_LXTAL: low speed crystal oscillator(LXTAL)
    \param[out] none
    \retval     none
*/
void rcu_osci_bypass_mode_disable(rcu_osci_type_enum osci)
{
    uint32_t reg;
    
    switch(osci){
    /* disable HXTAL to bypass mode */    
    case RCU_HXTAL:
        reg = RCU_CTL;
        RCU_CTL &= ~RCU_CTL_HXTALEN;
        RCU_CTL = (reg & ~RCU_CTL_HXTALBPS);
        break;
    /* disable LXTAL to bypass mode */
    case RCU_LXTAL:
        reg = RCU_BDCTL;
        RCU_BDCTL &= ~RCU_BDCTL_LXTALEN;
        RCU_BDCTL = (reg & ~RCU_BDCTL_LXTALBPS);
        break;
    default:
        break;
    }
}

/*!
    \brief      enable the RF HXTAL clock monitor 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_rf_hxtal_clock_monitor_enable(void)
{
    RCU_CTL |= RCU_CTL_RFCKMEN;
}

/*!
    \brief      disable the RF HXTAL clock monitor 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_rf_hxtal_clock_monitor_disable(void)
{
    RCU_CTL &= ~RCU_CTL_RFCKMEN;
}

/*!
    \brief      set the IRC16M adjust value
    \param[in]  irc16m_adjval: IRC16M adjust value, must be between 0 and 0x1F
      \arg        0x00 - 0x1F
    \param[out] none
    \retval     none
*/
void rcu_irc16m_adjust_value_set(uint32_t irc16m_adjval)
{
    uint32_t reg;
    
    reg = RCU_CTL;
    /* reset the IRC16MADJ bits and set according to irc16m_adjval */
    reg &= ~RCU_CTL_IRC16MADJ;
    RCU_CTL = (reg | ((irc16m_adjval & RCU_IRC16M_ADJUST_MASK) << RCU_IRC16M_ADJUST_OFFSET));
}

/*!
    \brief      unlock the voltage key
    \param[in]  none
    \param[out] none
    \retval     none
*/
void rcu_voltage_key_unlock(void)
{
    RCU_VKEY = RCU_VKEY_UNLOCK;
}

/*!
    \brief      deep-sleep mode voltage select
    \param[in]  dsvol: deep sleep mode voltage
                only one parameter can be selected which is shown as below:
      \arg        RCU_DEEPSLEEP_V_1_1: the core voltage is 1.1V
      \arg        RCU_DEEPSLEEP_V_1_0: the core voltage is 1.0V
      \arg        RCU_DEEPSLEEP_V_0_9: the core voltage is 0.9V
    \param[out] none
    \retval     none
*/
void rcu_deepsleep_voltage_set(uint32_t dsvol)
{    
    dsvol &= RCU_DSV_DSLPVS;
    RCU_DSV = dsvol;
}

/*!
    \brief      get the system clock, bus and peripheral clock frequency
    \param[in]  clock: the clock frequency which to get
                only one parameter can be selected which is shown as below:
      \arg        CK_SYS: system clock frequency
      \arg        CK_AHB: AHB clock frequency
      \arg        CK_APB1: APB1 clock frequency
      \arg        CK_APB2: APB2 clock frequency
      \arg        CK_USART0: USART0 clock frequency
      \arg        CK_I2C0: I2C0 clock frequency
    \param[out] none
    \retval     clock frequency of system, AHB, APB1, APB2
*/
uint32_t rcu_clock_freq_get(rcu_clock_freq_enum clock)
{
    uint32_t sws, ck_freq = 0U;
    uint32_t cksys_freq, ahb_freq, apb1_freq, apb2_freq;
    uint32_t usart0_freq = 0U,i2c0_freq = 0U;    
    uint32_t plldigpsc, idx, clk_exp;
    
    /* exponent of AHB, APB1 and APB2 clock divider */
    const uint8_t ahb_exp[16] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 7, 8, 9};
    const uint8_t apb1_exp[8] = {0, 0, 0, 0, 1, 2, 3, 4};
    const uint8_t apb2_exp[8] = {0, 0, 0, 0, 1, 2, 3, 4};

    const uint32_t plldig_oclk[4] = {192000000,240000000,320000000,480000000};

    sws = GET_BITS(RCU_CFG0, 2, 3);
    switch(sws){
    /* IRC16M is selected as CK_SYS */
    case SEL_IRC16M:
        cksys_freq = IRC16M_VALUE;
        break;
    /* HXTAL is selected as CK_SYS */
    case SEL_HXTAL:
        cksys_freq = HXTAL_VALUE;
        break;
    /* PLLP is selected as CK_SYS */
    case SEL_PLLDIG:
        idx = GET_BITS(RCU_PLLDIGCFG0,24,25);
        plldigpsc = GET_BITS(RCU_PLLDIGCFG0,26U,31U)+1;
        cksys_freq = plldig_oclk[idx]/plldigpsc;
        break;
    /* IRC16M is selected as CK_SYS */
    default:
        cksys_freq = IRC16M_VALUE;
        break;
    }
    /* calculate AHB clock frequency */
    idx = GET_BITS(RCU_CFG0, 4, 7);
    clk_exp = ahb_exp[idx];
    ahb_freq = cksys_freq >> clk_exp;
    
    /* calculate APB1 clock frequency */
    idx = GET_BITS(RCU_CFG0, 10, 12);
    clk_exp = apb1_exp[idx];
    apb1_freq = ahb_freq >> clk_exp;
    
    /* calculate APB2 clock frequency */
    idx = GET_BITS(RCU_CFG0, 13, 15);
    clk_exp = apb2_exp[idx];
    apb2_freq = ahb_freq >> clk_exp;
    
    /* return the clocks frequency */
    switch(clock){
    case CK_SYS:
        ck_freq = cksys_freq;
        break;
    case CK_AHB:
        ck_freq = ahb_freq;
        break;
    case CK_APB1:
        ck_freq = apb1_freq;
        break;
    case CK_APB2:
        ck_freq = apb2_freq;
        break;
    case CK_USART0:
        /* calculate USART0 clock frequency */
        if(RCU_USART0SRC_CKAPB1 == (RCU_CFG1 & RCU_CFG1_USART0SEL)){
            usart0_freq = apb1_freq;
        }else if(RCU_USART0SRC_CKSYS == (RCU_CFG1 & RCU_CFG1_USART0SEL)){
            usart0_freq = cksys_freq;
        }else if(RCU_USART0SRC_LXTAL == (RCU_CFG1 & RCU_CFG1_USART0SEL)){
            usart0_freq = LXTAL_VALUE;
        }else if(RCU_USART0SRC_IRC16M == (RCU_CFG1 & RCU_CFG1_USART0SEL)){
            usart0_freq = IRC16M_VALUE;
        }else{
        }
        ck_freq = usart0_freq;
        break;
    case CK_I2C0:
        /* calculate I2C0 clock frequency */
        if(RCU_I2C0SRC_CKAPB1 == (RCU_CFG1 & RCU_CFG1_I2C0SEL)){
            i2c0_freq = apb1_freq;
        }else if(RCU_I2C0SRC_CKSYS == (RCU_CFG1 & RCU_CFG1_I2C0SEL)){
            i2c0_freq = cksys_freq;
        }else if(RCU_I2C0SRC_IRC16M == (RCU_CFG1 & RCU_CFG1_I2C0SEL)){
            i2c0_freq = IRC16M_VALUE;
        }else{
        }
        ck_freq = i2c0_freq;
        break;
    default:
        break;
    }
    return ck_freq;
}
