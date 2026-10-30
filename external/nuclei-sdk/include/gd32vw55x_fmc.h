/*!
    \file    gd32vw55x_fmc.h
    \brief   definitions for the FMC

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

#ifndef GD32VW55X_FMC_H
#define GD32VW55X_FMC_H

#include "gd32vw55x.h"

/* FMC and option bytes definition */
#define FMC                             FMC_BASE                                         /*!< FMC base address */

/* registers definitions */
#define FMC_KEY                         REG32(FMC + 0x00000004U)                         /*!< FMC unlock key register */
#define FMC_OBKEY                       REG32(FMC + 0x00000008U)                         /*!< FMC option bytes unlock key register */
#define FMC_STAT                        REG32(FMC + 0x0000000CU)                         /*!< FMC status register */
#define FMC_CTL                         REG32(FMC + 0x00000010U)                         /*!< FMC control register */
#define FMC_ADDR                        REG32(FMC + 0x00000014U)                         /*!< FMC address register */
#define FMC_OBSTAT                      REG32(FMC + 0x0000001CU)                         /*!< FMC option byte status register */
#define FMC_OBR                         REG32(FMC + 0x00000040U)                         /*!< FMC option byte register */
#define FMC_OBUSER                      REG32(FMC + 0x00000044U)                         /*!< FMC option byte user register */
#define FMC_OBWRP0                      REG32(FMC + 0x00000048U)                         /*!< FMC option byte write protection area register 0 */
#define FMC_OBWRP1                      REG32(FMC + 0x0000004CU)                         /*!< FMC option byte write protection area register 1 */
#define FMC_NODEC0                      REG32(FMC + 0x00000070U)                         /*!< FMC NO-RTDEC region register 0 */
#define FMC_NODEC1                      REG32(FMC + 0x00000074U)                         /*!< FMC NO-RTDEC region register 1 */
#define FMC_NODEC2                      REG32(FMC + 0x00000078U)                         /*!< FMC NO-RTDEC region register 2 */
#define FMC_NODEC3                      REG32(FMC + 0x0000007CU)                         /*!< FMC NO-RTDEC region register 3 */
#define FMC_OFRG                        REG32(FMC + 0x00000080U)                         /*!< FMC offset region register */
#define FMC_OFVR                        REG32(FMC + 0x00000084U)                         /*!< FMC offset value register */
#define FMC_PID0                        REG32(FMC + 0x00000100U)                         /*!< FMC product ID0 register */
#define FMC_PID1                        REG32(FMC + 0x00000104U)                         /*!< FMC product ID1 register */
#define FMC_RFT0                        REG32(FMC + 0x00000108U)                         /*!< FMC RF Trim register 0 */
#define FMC_RFT1                        REG32(FMC + 0x0000010CU)                         /*!< FMC RF Trim register 1 */
#define FMC_WFT0                        REG32(FMC + 0x00000200U)                         /*!< FMC WiFi Trim register 0 */
#define FMC_WFT1                        REG32(FMC + 0x00000204U)                         /*!< FMC WiFi Trim register 1 */
#define FMC_WFT2                        REG32(FMC + 0x00000208U)                         /*!< FMC WiFi Trim register 2 */
#define FMC_WFT3                        REG32(FMC + 0x0000020CU)                         /*!< FMC WiFi Trim register 3 */
#define FMC_WFT4                        REG32(FMC + 0x00000210U)                         /*!< FMC WiFi Trim register 4 */
#define FMC_WFT5                        REG32(FMC + 0x00000214U)                         /*!< FMC WiFi Trim register 5 */
#define FMC_WFT6                        REG32(FMC + 0x00000218U)                         /*!< FMC WiFi Trim register 6 */
#define FMC_WFT7                        REG32(FMC + 0x0000021CU)                         /*!< FMC WiFi Trim register 7 */
#define FMC_WFT8                        REG32(FMC + 0x00000220U)                         /*!< FMC WiFi Trim register 8 */
#define FMC_WFT9                        REG32(FMC + 0x00000224U)                         /*!< FMC WiFi Trim register 9 */
#define FMC_WFT10                       REG32(FMC + 0x00000228U)                         /*!< FMC WiFi Trim register 10 */
#define FMC_WFT11                       REG32(FMC + 0x0000022CU)                         /*!< FMC WiFi Trim register 11 */
#define FMC_WFT12                       REG32(FMC + 0x00000230U)                         /*!< FMC WiFi Trim register 12 */
#define FMC_WFT13                       REG32(FMC + 0x00000234U)                         /*!< FMC WiFi Trim register 13 */
#define FMC_WFT14                       REG32(FMC + 0x00000238U)                         /*!< FMC WiFi Trim register 14 */
#define FMC_WFT15                       REG32(FMC + 0x0000023CU)                         /*!< FMC WiFi Trim register 15 */

/* bits definitions */
/* FMC_KEY */
#define FMC_KEY_KEY                     BITS(0,31)                                       /*!< FMC_CTL unlock key */

/* FMC_OBKEY */
#define FMC_OBKEY_OBKEY                 BITS(0,31)                                       /*!< option bytes unlock key */

/* FMC_STAT */
#define FMC_STAT_BUSY                   BIT(0)                                           /*!< flash busy flag */
#define FMC_STAT_WPERR                  BIT(4)                                           /*!< erase/program protection error flag */
#define FMC_STAT_ENDF                   BIT(5)                                           /*!< end of operation flag */
 
/* FMC_CTL */
#define FMC_CTL_PG                      BIT(0)                                           /*!< main flash program command */
#define FMC_CTL_PER                     BIT(1)                                           /*!< main flash page erase command */
#define FMC_CTL_MER                     BIT(2)                                           /*!< main flash mass erase command */
#define FMC_CTL_WTPG                    BIT(3)                                           /*!< WiFi trim program command */
#define FMC_CTL_START                   BIT(6)                                           /*!< send erase command to FMC */
#define FMC_CTL_LK                      BIT(7)                                           /*!< FMC_CTL lock */
#define FMC_CTL_OBWEN                   BIT(9)                                           /*!< FMC_OBR / FMC_OBUSER / FMC_OBWRPx (x=0,1) / FMC_NODECx (x=0,1,2,3) / FMC_OFRG / FMC_OFVR write enable */
#define FMC_CTL_ERRIE                   BIT(10)                                          /*!< error interrupt enable */
#define FMC_CTL_ENDIE                   BIT(12)                                          /*!< end of operation interrupt enable */
#define FMC_CTL_OBSTART                 BIT(14)                                          /*!< option bytes modification start */
#define FMC_CTL_OBRLD                   BIT(15)                                          /*!< option bytes reload */

/* FMC_ADDR */
#define FMC_ADDR_ADDR                   BITS(0,31)                                       /*!< address of flash to be erased / programmed */

/* FMC_OBSTAT */
#define FMC_OBSTAT_SPC                  BIT(1)                                           /*!< flash security protection level 1 state */
#define FMC_OBSTAT_WP                   BIT(2)                                           /*!< flash write / erase protection state, EFUSE config 32k write protection */

/* FMC_OBR */
#define FMC_OBR_SPC                     BITS(0,7)                                        /*!< option bytes security protection code */
#define FMC_OBR_NWDG_HW                 BIT(9)                                           /*!< option bytes NWDG_HW, watchdog status function */
#define FMC_OBR_NRST_STDBY              BIT(10)                                          /*!< option bytes NRST_STDBY, no reset generated when entering Standby mode*/
#define FMC_OBR_NSRT_DPSLP              BIT(11)                                          /*!< option bytes NRST_DPSLP, no reset generated when entering Deepsleep mode*/
#define FMC_OBR_SRAM1_RST               BIT(12)                                          /*!< option bytes SRAM1 erase when system reset */

/* FMC_OBUSER */
#define FMC_OBUSER_USER                 BITS(0,31)                                       /*!< option bytes user value */

/* FMC_OBWRP0 */
#define FMC_OBWRP0_WRP0_SPAGE           BITS(0,9)                                        /*!< start page of write protection area 0 */
#define FMC_OBWRP0_WRP0_EPAGE           BITS(16,25)                                      /*!< end page of write protection area 0 */

/* FMC_OBWRP1 */
#define FMC_OBWRP1_WRP1_SPAGE           BITS(0,9)                                        /*!< start page of write protection area 1 */
#define FMC_OBWRP1_WRP1_EPAGE           BITS(16,25)                                      /*!< end page of write protection area 1 */

/* FMC_NODEC0 */
#define FMC_NODEC0_NODEC0_SPAGE         BITS(0,9)                                        /*!< start page of NO-RTDEC region 0 */
#define FMC_NODEC0_NODEC0_EPAGE         BITS(16,25)                                      /*!< end page of NO-RTDEC region 0 */

/* FMC_NODEC1 */
#define FMC_NODEC1_NODEC1_SPAGE         BITS(0,9)                                        /*!< start page of NO-RTDEC region 1 */
#define FMC_NODEC1_NODEC1_EPAGE         BITS(16,25)                                      /*!< end page of NO-RTDEC region 1 */

/* FMC_NODEC2 */
#define FMC_NODEC2_NODEC2_SPAGE         BITS(0,9)                                        /*!< start page of NO-RTDEC region 2 */
#define FMC_NODEC2_NODEC2_EPAGE         BITS(16,25)                                      /*!< end page of NO-RTDEC region 2 */

/* FMC_NODEC3 */
#define FMC_NODEC3_NODEC3_SPAGE         BITS(0,9)                                        /*!< start page of NO-RTDEC region 3 */
#define FMC_NODEC3_NODEC3_EPAGE         BITS(16,25)                                      /*!< end page of NO-RTDEC region 3 */

/* FMC_OFRG */
#define FMC_OFRG_OF_SPAGE               BITS(0,12)                                       /*!< start page of offset region */
#define FMC_OFRG_OF_EPAGE               BITS(16,28)                                      /*!< end page of offset region */

/* FMC_OFVR */
#define FMC_OFVR_OF_VALUE               BITS(0,12)                                       /*!< offset value */

/* FMC_PID0 */
#define FMC_PID0_PID0                   BITS(0,31)                                       /*!< product ID 0 */

/* FMC_PID1 */
#define FMC_PID1_PID1                   BITS(0,15)                                       /*!< product ID 1 */

/* FMC_RFT0 */
#define FMC_RFT0_PABIAST0               BITS(0,3)                                        /*!< the PA(Power Amplifier) bias coarse tune value */
#define FMC_RFT0_PABIAST1               BITS(4,7)                                        /*!< the PA bias fine tune value */
#define FMC_RFT0_THECAL                 BITS(8,15)                                       /*!< thermal meter calibration value */
#define FMC_RFT0_WIFITXCAL              BITS(16,23)                                      /*!< WiFi transmit power calibration value */
#define FMC_RFT0_BLETXCAL               BITS(24,31)                                      /*!< BLE transmit power calibration value */

/* FMC_RFT1 */
#define FMC_RFT1_WIFIRXGCAL             BITS(0,3)                                        /*!< the WIFI receive gain calibration value */
#define FMC_RFT1_EFUSEID                BITS(4,7)                                        /*!< the EFUSE version ID */

/* FMC_WFT_TRIM */
#define FMC_WFT_WIFI_TRIM               BITS(0,31)                                       /*!< WiFi trim */

/* constants definitions */
/* fmc state */
typedef enum
{
    FMC_READY = 0,                                                                       /*!< the operation has been completed */
    FMC_BUSY,                                                                            /*!< the operation is in progress */
    FMC_WPERR,                                                                           /*!< erase/program protection error */
    FMC_TOERR,                                                                           /*!< timeout error */
    FMC_ERR                                                                           	 /*!< parameter error */
}fmc_state_enum;

/* unlock key */
#define UNLOCK_KEY0                     ((uint32_t)0x45670123U)                          /*!< unlock key 0 */
#define UNLOCK_KEY1                     ((uint32_t)0xCDEF89ABU)                          /*!< unlock key 1 */

/* read protection configuration */
#define FMC_NSPC                        ((uint8_t)0xAAU)                                 /*!< no security protection */
#define FMC_SPC_P1                      ((uint8_t)0xCCU)                                 /*!< security protection level 1 */

/* option byte wrtie protection area register x(x=0,1) */
#define OBWRP_INDEX0                    ((uint32_t)0x00000000U)                          /*!< FMC_OBWRP0 register index */
#define OBWRP_INDEX1                    ((uint32_t)0x00000001U)                          /*!< FMC_OBWRP1 register index */

/* NO RTDEC configuration register x(x=0,1,2,3) */
#define NODEC_INDEX0                    ((uint32_t)0x00000000U)                          /*!< FMC_NODEC0 register index */
#define NODEC_INDEX1                    ((uint32_t)0x00000001U)                          /*!< FMC_NODEC1 register index */
#define NODEC_INDEX2                    ((uint32_t)0x00000002U)                          /*!< FMC_NODEC2 register index */
#define NODEC_INDEX3                    ((uint32_t)0x00000003U)                          /*!< FMC_NODEC3 register index */

/* FMC flags */
#define OB_FLAG_NSPC                    ((uint32_t)0x00000000U)                          /*!< flash security protection level 0 state */
#define OB_FLAG_SPC1                    FMC_OBSTAT_SPC                                   /*!< flash security protection level 1 state */

/* FMC interrupt enable */
#define FMC_INT_ERR                     FMC_CTL_ERRIE                                    /*!< FMC error interrupt enable */
#define FMC_INT_END                     FMC_CTL_ENDIE                                    /*!< FMC end of operation interrupt enable */

/* FMC flags */
#define FMC_FLAG_BUSY                   FMC_STAT_BUSY                                    /*!< FMC busy flag */
#define FMC_FLAG_WPERR                  FMC_STAT_WPERR                                   /*!< FMC erase /program protection error flag */
#define FMC_FLAG_END                    FMC_STAT_ENDF                                    /*!< FMC end of operation flag */

/* FMC interrupt flags */
#define FMC_INT_FLAG_WPERR              FMC_STAT_WPERR                                   /*!< FMC erase/program protection error interrupt flag */
#define FMC_INT_FLAG_END                FMC_STAT_ENDF                                    /*!< FMC end of operation interrupt flag */

/* FMC timeout */
#define FMC_TIMEOUT_COUNT               ((uint32_t)0x01000000U)                          /*!< FMC timeout count value */

/* function declarations */
/* FMC main memory programming functions */
/* unlock the main FMC operation */
void fmc_unlock(void);
/* lock the main FMC operation */
void fmc_lock(void);
/* FMC erase page */
fmc_state_enum fmc_page_erase(uint32_t page_address);
/* FMC erase whole chip */
fmc_state_enum fmc_mass_erase(void);
/* FMC program a word at the corresponding address */
fmc_state_enum fmc_word_program(uint32_t address, uint32_t data);
/* FMC program continuously at the corresponding address */
fmc_state_enum fmc_continuous_program(uint32_t address, uint32_t data[], uint32_t size);
/*   enable FMC OBR function */
void fmc_obr_function_enable(uint32_t obr_function);
/*   disable FMC OBR function */
void fmc_obr_function_disable(uint32_t obr_function);
/* FMC option bytes programming functions */
/* unlock the option bytes operation */
void ob_unlock(void);
/* lock the option bytes operation */
void ob_lock(void);
/* send option bytes modification start command */
void ob_start(void);
/* reload option bytes */
void ob_reload(void);
/* configure the option bytes security protection */
fmc_state_enum ob_security_protection_config(uint8_t ob_spc);
/* program option bytes USER */
fmc_state_enum ob_user_write(uint32_t ob_user);
/* configure write protection pages */
fmc_state_enum ob_write_protection_config(uint32_t wrp_spage, uint32_t wrp_epage, uint32_t wrp_register_index);
/* configure NO-RTDEC pages */
void fmc_no_rtdec_config(uint32_t nodec_spage, uint32_t nodec_epage, uint32_t nodec_register_index);
/* configure offset region */
void fmc_offset_region_config(uint32_t of_spage, uint32_t of_epage);
/* configure offset value */
void fmc_offset_value_config(uint32_t of_value);
/* get calibration value */
void fmc_wifi_trim_cal_get(uint32_t *rft0_bletxcal, uint32_t *rft0_wftxcal, uint32_t *rft0_thecal, uint32_t *rft1_wfrxcal);
/* get Power Amplifier bias tune value */
void fmc_wifi_trim_pa_get(uint32_t *rft0_pa_tune0, uint32_t *rft0_pa_tune1);
/* get wifi trim */
fmc_state_enum fmc_wifi_trim_get(uint32_t size, uint32_t buf[]);
/* get product ID */
void fmc_pid_get(uint32_t *pid);
/* get option bytes write protection state, only applies to get the status of write/erase protection setting by EFUSE */
FlagStatus ob_write_protection_get(void);
/* get the value of option bytes USER */
uint32_t ob_user_get(void);
/* get option bytes security protection state */
FlagStatus ob_security_protection_flag_get(void);
/* FMC interrupts and flags management functions */
/* get FMC flag status */
FlagStatus fmc_flag_get(uint32_t flag);
/* clear the FMC flag */
void fmc_flag_clear(uint32_t flag);
/* enable FMC interrupt */
void fmc_interrupt_enable(uint32_t interrupt);
/* disable FMC interrupt */
void fmc_interrupt_disable(uint32_t interrupt);
/* get FMC interrupt flag */
FlagStatus fmc_interrupt_flag_get(uint32_t flag);
/* clear FMC interrupt flag */
void fmc_interrupt_flag_clear(uint32_t flag);
#endif /* GD32VW55X_FMC_H */
