/*!
    \file    gd32vw55x_pmu.h
    \brief   definitions for the PMU

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

#ifndef GD32VW55X_PMU_H
#define GD32VW55X_PMU_H

#include "gd32vw55x.h"

/* PMU definitions */
#define PMU                           PMU_BASE                              /*!< PMU base address */

/* registers definitions */
#define PMU_CTL0                      REG32((PMU) + 0x00000000U)            /*!< PMU control register 0 */
#define PMU_CS0                       REG32((PMU) + 0x00000004U)            /*!< PMU control and status register 0 */
#define PMU_CTL1                      REG32((PMU) + 0x00000008U)            /*!< PMU control register 1 */
#define PMU_CS1                       REG32((PMU) + 0x0000000CU)            /*!< PMU control and status register 1 */
#define PMU_PAR0                      REG32((PMU) + 0x00000010U)            /*!< PMU parameter register 0 */
#define PMU_PAR1                      REG32((PMU) + 0x00000014U)            /*!< PMU parameter register 1 */
#define PMU_PAR2                      REG32((PMU) + 0x00000018U)            /*!< PMU parameter register 2 */
#define PMU_RFCTL                     REG32((PMU) + 0x00000020U)            /*!< PMU RF control register */
#define PMU_RFPAR                     REG32((PMU) + 0x00000024U)            /*!< PMU RF timer parameter register */
#define PMU_INTF                      REG32((PMU) + 0x0000002CU)            /*!< PMU BLE interrupt flag register */
#define PMU_INTEN                     REG32((PMU) + 0x00000030U)            /*!< PMU BLE interrupt enable register */
#define PMU_INTC                      REG32((PMU) + 0x00000034U)            /*!< PMU BLE interrupt clear register */

/* bits definitions */
/* PMU_CTL0 */
#define PMU_CTL0_LDOLP                BIT(0)                                /*!< LDO low power mode */
#define PMU_CTL0_STBMOD               BIT(1)                                /*!< standby mode */
#define PMU_CTL0_WURST                BIT(2)                                /*!< wakeup flag reset */
#define PMU_CTL0_STBRST               BIT(3)                                /*!< standby flag reset */
#define PMU_CTL0_LVDEN                BIT(4)                                /*!< low voltage detector enable */
#define PMU_CTL0_LVDT                 BITS(5,7)                             /*!< low voltage detector threshold */
#define PMU_CTL0_BKPWEN               BIT(8)                                /*!< Backup Domain write enable */
#define PMU_CTL0_LDLP                 BIT(10)                               /*!< low-driver mode when use low power LDO */
#define PMU_CTL0_LDNP                 BIT(11)                               /*!< low-driver mode when use normal power LDO */
#define PMU_CTL0_LDEN                 BITS(18,19)                           /*!< low-driver mode enable in deep-sleep mode */

/* PMU_CS0 */
#define PMU_CS0_WUF                   BIT(0)                                /*!< wakeup flag */
#define PMU_CS0_STBF                  BIT(1)                                /*!< standby flag */
#define PMU_CS0_LVDF                  BIT(2)                                /*!< low voltage detector status flag */
#define PMU_CS0_WUPEN0                BIT(8)                                /*!< wakeup pin0 enable */
#define PMU_CS0_WUPEN1                BIT(9)                                /*!< wakeup pin1 enable */
#define PMU_CS0_WUPEN2                BIT(10)                               /*!< wakeup pin2 enable */
#define PMU_CS0_WUPEN3                BIT(11)                               /*!< wakeup pin3 enable */
#define PMU_CS0_LDOVSRF               BIT(14)                               /*!< LDO voltage select ready flag */
#define PMU_CS0_LDRF                  BITS(18,19)                           /*!< low-driver mode ready flag */

/* PMU_CTL1 */
#define PMU_CTL1_WPEN                 BIT(1)                                /*!< enable WIFI power */
#define PMU_CTL1_WPSLEEP              BIT(2)                                /*!< WIFI go to sleep */
#define PMU_CTL1_WPWAKE               BIT(3)                                /*!< wakeup WIFI */
#define PMU_CTL1_SRAM1PSLEEP          BIT(5)                                /*!< SRAM1 go to sleep */
#define PMU_CTL1_SRAM1PWAKE           BIT(6)                                /*!< wakeup SRAM1 */
#define PMU_CTL1_SRAM2PSLEEP          BIT(9)                                /*!< SRAM2 go to sleep */
#define PMU_CTL1_SRAM2PWAKE           BIT(10)                               /*!< wakeup SRAM2 */
#define PMU_CTL1_SRAM3PSLEEP          BIT(13)                               /*!< SRAM3 go to sleep */
#define PMU_CTL1_SRAM3PWAKE           BIT(14)                               /*!< wakeup SRAM3 */
#define PMU_CTL1_RETDIS               BIT(16)                               /*!< no retention register when WIFI power-off */
#define PMU_CTL1_WIFI_LPDS_ON         BIT(17)                               /*!< WIFI auto lpds flow on */
#define PMU_CTL1_WIFI_SRAM_RET        BIT(18)                               /*!< WIFI sram enter retention mode when deepsleep & WIFI sleep */
#define PMU_CTL1_SRAM0PSLEEP          BIT(19)                               /*!< SRAM0 go to sleep */
#define PMU_CTL1_SRAM0PWAKE           BIT(20)                               /*!< wakeup SRAM0 */
#define PMU_CTL1_BLE_SRAM_RET         BIT(21)                               /*!< BLE sram enter retention mode when deepsleep & BLE sleep */
#define PMU_CTL1_BLEPSLEEP            BIT(23)                               /*!< BLE go to sleep */
#define PMU_CTL1_BLEPWAKE             BIT(24)                               /*!< wakeup BLE */
#define PMU_CTL1_BLE_WAKEUP_REQ       BIT(25)                               /*!< BLE wakeup request */

/* PMU_CS1 */
#define PMU_CS1_WPS_SLEEP             BIT(2)                                /*!< WIFI is in sleep state */
#define PMU_CS1_WPS_ACTIVE            BIT(3)                                /*!< WIFI is in active state */
#define PMU_CS1_BLE_POWER_STATE       BIT(4)                                /*!< BLE power status */
#define PMU_CS1_SRAM1PS_SLEEP         BIT(5)                                /*!< SRAM1 is in sleep state */
#define PMU_CS1_SRAM1PS_ACTIVE        BIT(6)                                /*!< SRAM1 is in active state */
#define PMU_CS1_SRAM0PS_SLEEP         BIT(7)                                /*!< SRAM0 is in sleep state */
#define PMU_CS1_SRAM0PS_ACTIVE        BIT(8)                                /*!< SRAM0 is in active state */
#define PMU_CS1_SRAM2PS_SLEEP         BIT(9)                                /*!< SRAM2 is in sleep state */
#define PMU_CS1_SRAM2PS_ACTIVE        BIT(10)                               /*!< SRAM2 is in active state */
#define PMU_CS1_SRAM3PS_SLEEP         BIT(13)                               /*!< SRAM3 is in sleep state */
#define PMU_CS1_SRAM3PS_ACTIVE        BIT(14)                               /*!< SRAM3 is in active state */
#define PMU_CS1_BLEPS_SLEEP           BIT(16)                               /*!< BLE is in sleep state */
#define PMU_CS1_BLEPS_ACTIVE          BIT(17)                               /*!< BLE is in active state */

/* PMU_PAR0 */
#define PMU_PAR0_TWK_WL               BITS(8,15)                            /*!< Wakeup time of WIFI_OFF domain */
#define PMU_PAR0_TSW_IRCCNT           BITS(16,20)                           /*!< when enter deep-sleep, switch to IRC16M clock. Wait the IRC16M COUNTER */
#define PMU_PAR0_TWKEN                BIT(31)                               /*!< use software value when wake up WIFI_OFF or not */

/* PMU_PAR1 */
#define PMU_PAR1_TWK_SRAM1            BITS(0,7)                             /*!< wakeup time of SRAM1 domain */
#define PMU_PAR1_TWK_SRAM2            BITS(8,15)                            /*!< wakeup time of SRAM2 domain */
#define PMU_PAR1_TWK_SRAM3            BITS(16,23)                           /*!< wakeup time of SRAM3 domain */
#define PMU_PAR1_TWKSRAM1EN           BIT(29)                               /*!< use software value when wake up SRAM1 or not */
#define PMU_PAR1_TWKSRAM2EN           BIT(30)                               /*!< use software value when wake up SRAM2 or not */
#define PMU_PAR1_TWKSRAM3EN           BIT(31)                               /*!< use software value when wake up SRAM3 or not */

/* PMU_PAR2 */
#define PMU_PAR2_TWK_SRAM0            BITS(0,7)                             /*!< wakeup time of SRAM0 domain */
#define PMU_PAR2_TWK_BLE              BITS(8,15)                            /*!< wakeup time of BLE domain */
#define PMU_PAR2_TWKSRAM0EN           BIT(30)                               /*!< use software value when wake up SRAM0 or not */
#define PMU_PAR2_TWKBLEEN             BIT(31)                               /*!< use software value when wake up BLE or not */

/* PMU_RFCTL */
#define PMU_RFCTL_RFSWEN              BIT(0)                                /*!< RF software sequence enable */
#define PMU_RFCTL_RFFS                BIT(1)                                /*!< software force start, open RF power */
#define PMU_RFCTL_RFFC                BIT(2)                                /*!< software force close, close RF power */
#define PMU_RFCTL_MCU_PLLUP           BIT(3)                                /*!< software force open, open MCU PLL power */
#define PMU_RFCTL_MCU_PLLDOWN         BIT(4)                                /*!< software force close, close MCU PLL power */
#define PMU_RFCTL_BLESWEN             BIT(5)                                /*!< BLE software sequence enable */
#define PMU_RFCTL_RF_STATE            BITS(16,19)                           /*!< RF state */
#define PMU_RFCTL_MCU_STATE           BITS(20,22)                           /*!< MCU state */

/* PMU_RFPAR */
#define PMU_RFPAR_TIM1_PAR            BITS(0,6)                             /*!< RF timing parameter 1 */
#define PMU_RFPAR_TIM2_PAR            BITS(8,11)                            /*!< RF timing parameter 2 */
#define PMU_RFPAR_TIM3_PAR            BITS(16,17)                           /*!< RF timing parameter 3 */
#define PMU_RFPAR_TIM4_PAR            BITS(18,19)                           /*!< RF timing parameter 4 */
#define PMU_RFPAR_TIM5_PAR            BITS(20,21)                           /*!< RF timing parameter 5 */
#define PMU_RFPAR_TIM89_PAR           BITS(24,27)                           /*!< RF timing parameter 89 */
#define PMU_RFPAR_TIM7_PAR            BITS(28,30)                           /*!< RF timing parameter 7 */

/* PMU_INTF */
#define PMU_INTF_BLE_PS_FALLF         BIT(0)                                /*!< BLE power status falling edge interrupt flag */
#define PMU_INTF_BLE_PS_RISEF         BIT(1)                                /*!< BLE power status rising edge interrupt flag */

/* PMU_INTEN */
#define PMU_INTEN_BLE_PS_FALL_EN      BIT(0)                                /*!< BLE power status falling edge interrupt enable */
#define PMU_INTEN_BLE_PS_RISE_EN      BIT(1)                                /*!< BLE power status rising edge interrupt enable */

/* PMU_INTC */
#define PMU_INTC_BLE_PS_FALLFC        BIT(0)                                /*!< clear BLE power status falling edge interrupt flag */
#define PMU_INTC_BLE_PS_RISEFC        BIT(1)                                /*!< clear BLE power status rising edge interrupt flag */

/* constants definitions */
/* PMU LDO definitions */
#define PMU_LDO_NORMAL                ((uint32_t)0x00000000U)               /*!< LDO normal work when PMU enter deepsleep mode */
#define PMU_LDO_LOWPOWER              PMU_CTL0_LDOLP                        /*!< LDO work at low power status when PMU enter deepsleep mode */

/* PMU low voltage detector threshold definitions */
#define CTL0_LVDT(regval)             (BITS(5,7)&((uint32_t)(regval)<<5))
#define PMU_LVDT_0                    CTL0_LVDT(0)                          /*!< voltage threshold is 2.1V */
#define PMU_LVDT_1                    CTL0_LVDT(1)                          /*!< voltage threshold is 2.3V */
#define PMU_LVDT_2                    CTL0_LVDT(2)                          /*!< voltage threshold is 2.4V */
#define PMU_LVDT_3                    CTL0_LVDT(3)                          /*!< voltage threshold is 2.6V */
#define PMU_LVDT_4                    CTL0_LVDT(4)                          /*!< voltage threshold is 2.7V */
#define PMU_LVDT_5                    CTL0_LVDT(5)                          /*!< voltage threshold is 2.9V */
#define PMU_LVDT_6                    CTL0_LVDT(6)                          /*!< voltage threshold is 3.0V */
#define PMU_LVDT_7                    CTL0_LVDT(7)                          /*!< voltage threshold is 3.1V */

/* PMU low-driver mode when use low power LDO */
#define CTL0_LDLP(regval)             (BIT(10)&((uint32_t)(regval)<<10))
#define PMU_NORMALDR_LOWPWR           CTL0_LDLP(0)                          /*!< normal driver when use low power LDO */
#define PMU_LOWDR_LOWPWR              CTL0_LDLP(1)                          /*!< low-driver mode enabled when LDEN is 11 and use low power LDO */

/* PMU low-driver mode when use normal power LDO */
#define CTL0_LDNP(regval)             (BIT(11)&((uint32_t)(regval)<<11))
#define PMU_NORMALDR_NORMALPWR        CTL0_LDNP(0)                          /*!< normal driver when use normal power LDO */
#define PMU_LOWDR_NORMALPWR           CTL0_LDNP(1)                          /*!< low-driver mode enabled when LDEN is 11 and use normal power LDO */

/* Low-driver mode in deep-sleep mode */
#define PMU_LOWDRIVER_DISABLE         ((uint32_t)0x00000000U)               /*!< low-driver mode disable in deep-sleep mode */
#define PMU_LOWDRIVER_ENABLE          PMU_CTL0_LDEN                         /*!< low-driver mode enable in deep-sleep mode */

/* PMU wakeup pin definitions */
#define PMU_WAKEUP_PIN0               PMU_CS0_WUPEN0                        /*!< WKUP Pin 0 (PA0) enable */
#define PMU_WAKEUP_PIN1               PMU_CS0_WUPEN1                        /*!< WKUP Pin 1 (PA15) enable */
#define PMU_WAKEUP_PIN2               PMU_CS0_WUPEN2                        /*!< WKUP Pin 2 (PA7) enable */
#define PMU_WAKEUP_PIN3               PMU_CS0_WUPEN3                        /*!< WKUP Pin 3 (PA12) enable */

/* PMU low-drive mode ready flag definitions */
#define CS0_LDRF(regval)              (BITS(18,19)&((uint32_t)(regval)<<18))
#define PMU_LDRF_NORMAL               CS0_LDRF(0)                           /*!< normal driver in deep-sleep mode */
#define PMU_LDRF_LOWDRIVER            CS0_LDRF(3)                           /*!< low-driver mode in deep-sleep mode */

/* PMU WIFI SRAM control */
#define PMU_WIFI_SLEEP                PMU_CTL1_WPSLEEP                      /*!< WIFI go to sleep */
#define PMU_WIFI_WAKE                 PMU_CTL1_WPWAKE                       /*!< wakeup WIFI */
#define PMU_SRAM1_SLEEP               PMU_CTL1_SRAM1PSLEEP                  /*!< SRAM1 go to sleep */
#define PMU_SRAM1_WAKE                PMU_CTL1_SRAM1PWAKE                   /*!< wakeup SRAM1 */
#define PMU_SRAM2_SLEEP               PMU_CTL1_SRAM2PSLEEP                  /*!< SRAM2 go to sleep */
#define PMU_SRAM2_WAKE                PMU_CTL1_SRAM2PWAKE                   /*!< wakeup SRAM2 */
#define PMU_SRAM3_SLEEP               PMU_CTL1_SRAM3PSLEEP                  /*!< SRAM3 go to sleep */
#define PMU_SRAM3_WAKE                PMU_CTL1_SRAM3PWAKE                   /*!< wakeup SRAM3 */
#define PMU_SRAM0_SLEEP               PMU_CTL1_SRAM0PSLEEP                  /*!< SRAM0 go to sleep */
#define PMU_SRAM0_WAKE                PMU_CTL1_SRAM0PWAKE                   /*!< wakeup SRAM0 */
#define PMU_BLE_SLEEP                 PMU_CTL1_BLEPSLEEP                    /*!< BLE go to sleep */
#define PMU_BLE_WAKE                  PMU_CTL1_BLEPWAKE                     /*!< wakeup BLE */

/* BLE RF sequence definitions */
#define PMU_BLE_RF_HARDWARE           ((uint32_t)0x00000000U)               /*!< enable RF by BLE hardware */
#define PMU_BLE_RF_SOFTWARE           PMU_RFCTL_BLESWEN                     /*!< enable RF by software */

/* RF sequence definitions */
#define PMU_RF_HARDWARE               ((uint32_t)0x00000000U)               /*!< enable RF hardware sequence */
#define PMU_RF_SOFTWARE               PMU_RFCTL_RFSWEN                      /*!< enable RF software sequence */

/* RF force definitions */
#define PMU_RF_FORCE_OPEN             PMU_RFCTL_RFFS                        /*!< software force start, open RF power */
#define PMU_RF_FORCE_CLOSE            PMU_RFCTL_RFFC                        /*!< software force close, close RF power */

/* MCU PLL force definitions */
#define PMU_PLL_FORCE_OPEN            PMU_RFCTL_MCU_PLLUP                   /*!< software force start, open MCU PLL power */
#define PMU_PLL_FORCE_CLOSE           PMU_RFCTL_MCU_PLLDOWN                 /*!< software force close, close MCU PLL power */

/* PMU flag definitions */
#define PMU_FLAG_WAKEUP               PMU_CS0_WUF                           /*!< wakeup flag status */
#define PMU_FLAG_STANDBY              PMU_CS0_STBF                          /*!< standby flag status */
#define PMU_FLAG_LVD                  PMU_CS0_LVDF                          /*!< LVD flag status */
#define PMU_FLAG_LDOVSRF              PMU_CS0_LDOVSRF                       /*!< LDO voltage select ready flag */
#define PMU_FLAG_LDRF                 PMU_CS0_LDRF                          /*!< low-driver mode ready flag */
#define PMU_FLAG_WIFI_SLEEP           (BIT(31) | PMU_CS1_WPS_SLEEP)      /*!< WIFI is in sleep state */
#define PMU_FLAG_WIFI_ACTIVE          (BIT(31) | PMU_CS1_WPS_ACTIVE)     /*!< WIFI is in active state */
#define PMU_FLAG_BLE_POWER            (BIT(31) | PMU_CS1_BLE_POWER_STATUS)  /*!< BLE power status */
#define PMU_FLAG_SRAM1_SLEEP          (BIT(31) | PMU_CS1_SRAM1PS_SLEEP)     /*!< SRAM1 is in sleep state */
#define PMU_FLAG_SRAM1_ACTIVE         (BIT(31) | PMU_CS1_SRAM1PS_ACTIVE)    /*!< SRAM1 is in active state */
#define PMU_FLAG_SRAM0_SLEEP          (BIT(31) | PMU_CS1_SRAM0PS_SLEEP)     /*!< SRAM0 is in sleep state */
#define PMU_FLAG_SRAM0_ACTIVE         (BIT(31) | PMU_CS1_SRAM0PS_ACTIVE)    /*!< SRAM0 is in active state */
#define PMU_FLAG_SRAM2_SLEEP          (BIT(31) | PMU_CS1_SRAM2PS_SLEEP)     /*!< SRAM2 is in sleep state */
#define PMU_FLAG_SRAM2_ACTIVE         (BIT(31) | PMU_CS1_SRAM2PS_ACTIVE)    /*!< SRAM2 is in active state */
#define PMU_FLAG_SRAM3_SLEEP          (BIT(31) | PMU_CS1_SRAM3PS_SLEEP)     /*!< SRAM3 is in sleep state */
#define PMU_FLAG_SRAM3_ACTIVE         (BIT(31) | PMU_CS1_SRAM3PS_ACTIVE)    /*!< SRAM3 is in active state */
#define PMU_FLAG_BLE_SLEEP            (BIT(31) | PMU_CS1_BLEPS_SLEEP)       /*!< BLE is in sleep state */
#define PMU_FLAG_BLE_ACTIVE           (BIT(31) | PMU_CS1_BLEPS_ACTIVE)      /*!< BLE is in active state */
#define PMU_FLAG_BLE_POWER_FALL       (BIT(30) | PMU_INTF_BLE_PS_FALLF)     /*!< BLE power status falling edge flag */
#define PMU_FLAG_BLE_POWER_RISE       (BIT(30) | PMU_INTF_BLE_PS_RISEF)     /*!< BLE power status rising edge flag */

/* PMU flag reset definitions */
#define PMU_FLAG_RESET_WAKEUP         PMU_CTL0_WURST                        /*!< wakeup flag reset */
#define PMU_FLAG_RESET_STANDBY        PMU_CTL0_STBRST                       /*!< standby flag reset */
#define PMU_FLAG_RESET_LDRF           PMU_CS0_LDRF                          /*!< low-driver mode ready flag reset */

/* PMU interrupt definitions */
#define PMU_INT_BLE_POWER_FALL        PMU_INTEN_BLE_PS_FALL_EN               /*!< BLE power status falling edge interrupt */
#define PMU_INT_BLE_POWER_RISE        PMU_INTEN_BLE_PS_RISE_EN               /*!< BLE power status rising edge interrupt */

/* PMU interrupt flag definitions */
#define PMU_INT_FLAG_BLE_POWER_FALL   PMU_INTF_BLE_PS_FALLF                 /*!< BLE power status falling edge interrupt flag */
#define PMU_INT_FLAG_BLE_POWER_RISE   PMU_INTF_BLE_PS_RISEF                 /*!< BLE power status rising edge interrupt flag */

/* PMU interrupt flag reset definitions */
#define PMU_INT_FLAG_RESET_BLE_POWER_FALL      PMU_INTC_BLE_PS_FALLFC        /*!< BLE power status falling edge interrupt flag reset */
#define PMU_INT_FLAG_RESET_BLE_POWER_RISE      PMU_INTC_BLE_PS_RISEFC        /*!< BLE power status rising edge interrupt flag reset */

/* PMU command constants definitions */
#define WFI_CMD                       ((uint8_t)0x00U)                      /*!< use WFI command */
#define WFE_CMD                       ((uint8_t)0x01U)                      /*!< use WFE command */

/* function declarations */
/* reset PMU register */
void pmu_deinit(void);

/* LVD functions */
/* select low voltage detector threshold */
void pmu_lvd_select(uint32_t lvdt_n);
/* enable PMU LVD */
void pmu_lvd_enable(void);
/* disable PMU LVD */
void pmu_lvd_disable(void);

/* enable write access to the registers in backup domain */
void pmu_backup_write_enable(void);
/* disable write access to the registers in backup domain */
void pmu_backup_write_disable(void);

/* set PMU mode */
/* PMU work in sleep mode */
void pmu_to_sleepmode(uint8_t sleepmodecmd);
/* PMU work in deep-sleep mode */
void pmu_to_deepsleepmode(uint32_t ldo, uint32_t lowdrive, uint8_t deepsleepmodecmd);
/* PMU work in standby mode */
void pmu_to_standbymode(uint8_t standbymodecmd);
/* enable wakeup pin */
void pmu_wakeup_pin_enable(uint32_t wakeup_pin);
/* disable wakeup pin */
void pmu_wakeup_pin_disable(uint32_t wakeup_pin);

/* WIFI & BLE & SRAM functions */
/* enable WIFI power */
void pmu_wifi_power_enable(void);
/* disable WIFI power */
void pmu_wifi_power_disable(void);
/* WIFI & SRAM low power control */
void pmu_wifi_sram_control(uint32_t wifi_sram);
/* BLE low power control */
void pmu_ble_control(uint32_t ble);
/* enable BLE wakeup request */
void pmu_ble_wakeup_request_enable(void);
/* disable BLE wakeup request */
void pmu_ble_wakeup_request_disable(void);

/* MCU PLL power functions */
/* enable MCU PLL power force open/close */
void pmu_pll_force_enable(uint32_t force);
/* disable MCU PLL power open/close force */
void pmu_pll_force_disable(uint32_t force);

/* RF functions */
/* configure BLE RF sequence */
void pmu_ble_rf_config(uint32_t mode);
/* enable RF sequence force open/close */
void pmu_rf_force_enable(uint32_t force);
/* disable RF sequence open/close force */
void pmu_rf_force_disable(uint32_t force);
/* configure RF sequence */
void pmu_rf_sequence_config(uint32_t mode);

/* interrupt and flag functions */
/* get flag status */
FlagStatus pmu_flag_get(uint32_t flag);
/* clear flag bit */
void pmu_flag_clear(uint32_t flag);
/* enable PMU interrupt */
void pmu_interrupt_enable(uint32_t interrupt);
/* disable PMU interrupt */
void pmu_interrupt_disable(uint32_t interrupt);
/* get PMU interrupt flag */
FlagStatus pmu_interrupt_flag_get(uint32_t int_flag);
/* clear PMU interrupt flag */
void pmu_interrupt_flag_clear(uint32_t int_flag);

#endif /* GD32VW55X_PMU_H */
