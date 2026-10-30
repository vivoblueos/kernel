/*!
    \file    gd32vw55x_efuse.h
    \brief   definitions for the EFUSE

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

#ifndef GD32VW55X_EFUSE_H
#define GD32VW55X_EFUSE_H

#include "gd32vw55x.h"

/* EFUSE definitions */
#define EFUSE                              (EFUSE_BASE)                      /*!< EFUSE base address */

/* registers definitions */
#define EFUSE_CS                           REG32(EFUSE + 0x00000000U)        /*!< EFUSE control and status register */
#define EFUSE_ADDR                         REG32(EFUSE + 0x00000004U)        /*!< EFUSE address register */
#define EFUSE_CTL0                         REG32(EFUSE + 0x00000008U)        /*!< EFUSE control 0 register */
#define EFUSE_CTL1                         REG32(EFUSE + 0x0000000CU)        /*!< EFUSE control 1 register */
#define EFUSE_FPCTL                        REG32(EFUSE + 0x00000010U)        /*!< EFUSE flash protection control register */
#define EFUSE_USERCTL                      REG32(EFUSE + 0x00000014U)        /*!< EFUSE user control register */

#define EFUSE_RES0                         REG32(EFUSE + 0x00000018U)        /*!< EFUSE reserved register0 */
#define EFUSE_RES1                         REG32(EFUSE + 0x0000001CU)        /*!< EFUSE reserved register1 */
#define EFUSE_RES2                         REG32(EFUSE + 0x00000020U)        /*!< EFUSE reserved register2 */

#define EFUSE_AESKEY0                      REG32(EFUSE + 0x00000024U)        /*!< EFUSE firmware AES key register0 */
#define EFUSE_AESKEY1                      REG32(EFUSE + 0x00000028U)        /*!< EFUSE firmware AES key register1 */
#define EFUSE_AESKEY2                      REG32(EFUSE + 0x0000002CU)        /*!< EFUSE firmware AES key register2 */
#define EFUSE_AESKEY3                      REG32(EFUSE + 0x00000030U)        /*!< EFUSE firmware AES key register3 */

#define EFUSE_ROTPKKEY0                    REG32(EFUSE + 0x00000034U)        /*!< EFUSE RoTPK key register0 */
#define EFUSE_ROTPKKEY1                    REG32(EFUSE + 0x00000038U)        /*!< EFUSE RoTPK key register1 */
#define EFUSE_ROTPKKEY2                    REG32(EFUSE + 0x0000003CU)        /*!< EFUSE RoTPK key register2 */
#define EFUSE_ROTPKKEY3                    REG32(EFUSE + 0x00000040U)        /*!< EFUSE RoTPK key register3 */
#define EFUSE_ROTPKKEY4                    REG32(EFUSE + 0x00000044U)        /*!< EFUSE RoTPK key register4 */
#define EFUSE_ROTPKKEY5                    REG32(EFUSE + 0x00000048U)        /*!< EFUSE RoTPK key register5 */
#define EFUSE_ROTPKKEY6                    REG32(EFUSE + 0x0000004CU)        /*!< EFUSE RoTPK key register6 */
#define EFUSE_ROTPKKEY7                    REG32(EFUSE + 0x00000050U)        /*!< EFUSE RoTPK key register7 */

#define EFUSE_PUID0                        REG32(EFUSE + 0x00000054U)        /*!< EFUSE product UID register0 */
#define EFUSE_PUID1                        REG32(EFUSE + 0x00000058U)        /*!< EFUSE product UID register1 */
#define EFUSE_PUID2                        REG32(EFUSE + 0x0000005CU)        /*!< EFUSE product UID register2 */
#define EFUSE_PUID3                        REG32(EFUSE + 0x00000060U)        /*!< EFUSE product UID register3 */

#define EFUSE_HUKKEY0                      REG32(EFUSE + 0x00000064U)        /*!< EFUSE HUK key register0 */
#define EFUSE_HUKKEY1                      REG32(EFUSE + 0x00000068U)        /*!< EFUSE HUK key register1 */
#define EFUSE_HUKKEY2                      REG32(EFUSE + 0x0000006CU)        /*!< EFUSE HUK key register2 */
#define EFUSE_HUKKEY3                      REG32(EFUSE + 0x00000070U)        /*!< EFUSE HUK key register3 */

#define EFUSE_USER_DATA0                   REG32(EFUSE + 0x00000074U)        /*!< EFUSE user data register0 */
#define EFUSE_USER_DATA1                   REG32(EFUSE + 0x00000078U)        /*!< EFUSE user data register1 */
#define EFUSE_USER_DATA2                   REG32(EFUSE + 0x0000007CU)        /*!< EFUSE user data register2 */
#define EFUSE_USER_DATA3                   REG32(EFUSE + 0x00000080U)        /*!< EFUSE user data register3 */
#define EFUSE_USER_DATA4                   REG32(EFUSE + 0x00000084U)        /*!< EFUSE user data register4 */
#define EFUSE_USER_DATA5                   REG32(EFUSE + 0x00000088U)        /*!< EFUSE user data register5 */
#define EFUSE_USER_DATA6                   REG32(EFUSE + 0x0000008CU)        /*!< EFUSE user data register6 */
#define EFUSE_USER_DATA7                   REG32(EFUSE + 0x00000090U)        /*!< EFUSE user data register7 */

#define EFUSE_BOOTADDR                     REG32(EFUSE + 0x00000124U)        /*!< EFUSE boot address register */

/* bits definitions */
/* EFUSE_CS */
#define EFUSE_CS_EFSTR                     BIT(0)                            /*!< start EFUSE operation */
#define EFUSE_CS_EFRW                      BIT(1)                            /*!< selection of EFUSE operation */
#define EFUSE_CS_PGIF                      BIT(16)                           /*!< programming operation completion flag */
#define EFUSE_CS_RDIF                      BIT(17)                           /*!< read operation completion flag */
#define EFUSE_CS_OVBERIF                   BIT(18)                           /*!< overstep boundary error flag */
#define EFUSE_CS_PGIE                      BIT(20)                           /*!< enable bit for programming operation completed interrupt */
#define EFUSE_CS_RDIE                      BIT(21)                           /*!< enable bit for read operation completed interrupt */
#define EFUSE_CS_OVBERIE                   BIT(22)                           /*!< enable bit for overstep boundary error interrupt */
#define EFUSE_CS_PGIC                      BIT(24)                           /*!< clear bit for programming operation completed interrupt flag */
#define EFUSE_CS_RDIC                      BIT(25)                           /*!< clear bit for read operation completed interrupt flag */
#define EFUSE_CS_OVBERIC                   BIT(26)                           /*!< clear bit for overstep boundary error interrupt flag */

/* EFUSE_ADDR */
#define EFUSE_ADDR_EFADDR                  BITS(0,5)                         /*!< read or write EFUSE data start address */
#define EFUSE_ADDR_EFSIZE                  BITS(8,13)                        /*!< read or write EFUSE data size */

/* EFUSE_CTL0 */
#define EFUSE_CTL0_EFSB                    BIT(0)                            /*!< boot from secure boot */
#define EFUSE_CTL0_EFBOOTLK                BIT(1)                            /*!< EFUSE boot bits lock bit */
#define EFUSE_CTL0_EFBOOT1                 BIT(2)                            /*!< EFUSE boot1 */
#define EFUSE_CTL0_SWBOOT1                 BIT(3)                            /*!< enable bit of EFUSE boot1 */
#define EFUSE_CTL0_EFBOOT0                 BIT(4)                            /*!< EFUSE boot0 */
#define EFUSE_CTL0_SWBOOT0                 BIT(5)                            /*!< enable bit of EFUSE boot0 */

/* EFUSE_CTL1 */
#define EFUSE_CTL1_NDBG                    BIT(1)                            /*!< debugging permission setting */
#define EFUSE_CTL1_ROTLK                   BIT(2)                            /*!< EFUSE_ROTPKKEY register lock bit */
#define EFUSE_CTL1_VFIMG                   BIT(6)                            /*!< verify firmware image */
#define EFUSE_CTL1_VFCERT                  BIT(7)                            /*!< verify firmware certificate */

/* EFUSE_FPCTL */
#define EFUSE_FPCTL_FP                     BITS(0,2)                         /*!< EFUSE flash protection value */

/* EFUSE_USERCTL */
#define EFUSE_USERCTL_SBCLK                BIT(0)                            /*!< secure boot clock source selection */
#define EFUSE_USERCTL_LOGUART              BIT(1)                            /*!< secure boot log UART selection */
#define EFUSE_USERCTL_EFOPLK               BIT(3)                            /*!< EFUSE_FPCTL and EFUSE_USERCTL register lock bit */
#define EFUSE_USERCTL_AESEN                BIT(5)                            /*!< lock EFUSE_AESKEY register and enable AES decrypt function */
#define EFUSE_USERCTL_UDLK                 BIT(6)                            /*!< EFUSE_USER_DATA register lock bit */

/* EFUSE_RES_RES */
#define EFUSE_RES_RES                      BITS(0,31)                        /*!< EFUSE reserved data */

/* EFUSE_AESKEY */
#define EFUSE_AESKEY_AESKEY                BITS(0,31)                        /*!< EFUSE AES key value */

/* EFUSE_ROTPKKEY */
#define EFUSE_ROTPKKEY_RKEY                BITS(0,31)                        /*!< EFUSE ROTPK or its hash value */

/* EFUSE_PUID */
#define EFUSE_PUID_UID                     BITS(0,31)                        /*!< EFUSE MCU UID value */

/* EFUSE_HUKKEY */
#define EFUSE_HUKKEY_HKEY                  BITS(0,31)                        /*!< EFUSE HUK value */

/* EFUSE_USER_DATA */
#define EFUSE_USER_DATA_USERDATA           BITS(0,31)                        /*!< EFUSE USER_DATA value */

/* constants definitions */
/* EFUSE flag enum */
typedef enum {
    EFUSE_PGIF    = EFUSE_CS_PGIF,                                           /*!< programming operation completion flag */
    EFUSE_RDIF    = EFUSE_CS_RDIF,                                           /*!< read operation completion flag */
    EFUSE_OVBERIF = EFUSE_CS_OVBERIF,                                        /*!< overstep boundary error flag */
} efuse_flag_enum;

/* EFUSE flag clear enum */
typedef enum {
    EFUSE_PGIC    = EFUSE_CS_PGIC,                                           /*!< clear programming operation completion flag */
    EFUSE_RDIC    = EFUSE_CS_RDIC,                                           /*!< clear read operation completion flag */
    EFUSE_OVBERIC = EFUSE_CS_OVBERIC,                                        /*!< clear overstep boundary error flag */
} efuse_clear_flag_enum;

/* EFUSE interrupt enum */
typedef enum {
    EFUSE_INTEN_PG    = EFUSE_CS_PGIE,                                       /*!< programming operation completion interrupt */
    EFUSE_INTEN_RD    = EFUSE_CS_RDIE,                                       /*!< read operation completion interrupt */
    EFUSE_INTEN_OVBER = EFUSE_CS_OVBERIE,                                    /*!< overstep boundary error interrupt */
} efuse_int_enum;

/* EFUSE interrupt flag enum */
typedef enum {
    EFUSE_INT_PGIF    = EFUSE_CS_PGIF,                                       /*!< programming operation completion interrupt flag */
    EFUSE_INT_RDIF    = EFUSE_CS_RDIF,                                       /*!< read operation completion interrupt flag */
    EFUSE_INT_OVBERIF = EFUSE_CS_OVBERIF,                                    /*!< overstep boundary error interrupt flag */
} efuse_int_flag_enum;

/* EFUSE interrupt flag clear enum */
typedef enum {
    EFUSE_INT_PGIC    = EFUSE_CS_PGIC,                                       /*!< clear programming operation completion interrupt flag */
    EFUSE_INT_RDIC    = EFUSE_CS_RDIC,                                       /*!< clear read operation completion interrupt flag */
    EFUSE_INT_OVBERIC = EFUSE_CS_OVBERIC,                                    /*!< clear overstep boundary error interrupt flag */
} efuse_clear_int_flag_enum;

/* EFUSE register lock enum */
typedef enum {
    EFUSE_BOOT_LOCK          = EFUSE_CTL0_EFBOOTLK,                          /*!< EFUSE boot bits lock bit */
    EFUSE_ROTPKKEY_LOCK      = EFUSE_CTL1_ROTLK,                             /*!< EFUSE_ROTPKKEY register lock bit */
    EFUSE_USER_DATA_LOCK     = EFUSE_USERCTL_UDLK,                           /*!< EFUSE_USER_DATA register lock bit */
    EFUSE_AESKEY_LOCK        = EFUSE_USERCTL_AESEN,                          /*!< EFUSE_AESKEY register lock bit */
    EFUSE_FPCTL_USERCTL_LOCK = EFUSE_USERCTL_EFOPLK,                         /*!< EFUSE_FPCTL and EFUSE_USERCTL register lock bit */
} efuse_reg_lock_enum;

#define EFUSE_MAX_SIZE                     ((uint32_t)0x00000020U)           /*!< the maximum length of a single field in EFUSE */

#define EFUSE_CTL0_ADDR                    ((uint32_t)0x00000000U)           /*!< EFUSE control0 address */
#define EFUSE_CTL1_ADDR                    ((uint32_t)0x00000001U)           /*!< EFUSE control1 address */
#define FP_ADDR                            ((uint32_t)0x00000002U)           /*!< flash protection address */
#define USER_CTL_ADDR                      ((uint32_t)0x00000003U)           /*!< user control address */
#define RESERVED_ADDR                      ((uint32_t)0x00000004U)           /*!< reserved address */
#define AES_KEY_ADDR                       ((uint32_t)0x00000010U)           /*!< AES key address */
#define ROTPK_ADDR                         ((uint32_t)0x00000020U)           /*!< ROTPK address */
#define MCU_UID_ADDR                       ((uint32_t)0x00000040U)           /*!< MCU unique ID address */
#define HUK_ADDR                           ((uint32_t)0x00000050U)           /*!< HUK address */
#define USER_DATA_ADDR                     ((uint32_t)0x00000060U)           /*!< user data address */
#define END_ADDR                           ((uint32_t)0x00000080U)           /*!< EFUSE end address */

/* function declarations */
/* EFUSE read and write functions */
/* read EFUSE value */
ErrStatus efuse_read(uint32_t ef_addr, uint32_t size, uint32_t buf[]);
/* write EFUSE */
ErrStatus efuse_write(uint32_t ef_addr, uint32_t size, uint32_t buf[]);

/* EFUSE operation functions */
/* configure boot */
ErrStatus efuse_boot_config(uint32_t size, uint8_t bt_value[]);
/* configure efuse control1 */
ErrStatus efuse_control1_config(uint32_t size, uint8_t ctl[]);
/* configure flash protection */
ErrStatus efuse_fp_config(uint32_t size, uint8_t fp_value[]);
/* configure user control */
ErrStatus efuse_user_control_config(uint32_t size, uint8_t user_ctl[]);
/* write MCU reserved value */
ErrStatus efuse_res_write(uint32_t size, uint8_t buf[]);
/* write AES key */
ErrStatus efuse_aes_key_write(uint32_t size, uint8_t buf[]);
/* write ROTPK key */
ErrStatus efuse_rotpk_key_write(uint32_t size, uint8_t buf[]);
/* write user data */
ErrStatus efuse_user_data_write(uint32_t size, uint8_t buf[]);
/* read MCU reserved value */
void efuse_res_read(uint32_t buf[]);
/* read AES key */
void efuse_aes_key_read(uint32_t buf[]);
/* read ROTPK key */
void efuse_rotpk_key_read(uint32_t buf[]);
/* read puid */
void efuse_puid_read(uint32_t buf[]);
/* read huk key */
void efuse_huk_key_read(uint32_t buf[]);
/* read user data */
void efuse_user_data_read(uint32_t buf[]);
/* get boot address information */
uint32_t efuse_boot_address_get(void);
/* lock efuse filed */
void efuse_lock_config(efuse_reg_lock_enum source);

/* flag and interrupt functions */
/* check EFUSE flag is set or not */
FlagStatus efuse_flag_get(efuse_flag_enum flag);
/* clear EFUSE pending flag */
void efuse_flag_clear(efuse_clear_flag_enum flag);
/* enable EFUSE interrupt */
void efuse_interrupt_enable(efuse_int_enum source);
/* disable EFUSE interrupt */
void efuse_interrupt_disable(efuse_int_enum source);
/* check EFUSE interrupt flag is set or not */
FlagStatus efuse_interrupt_flag_get(efuse_int_flag_enum int_flag);
/* clear EFUSE pending interrupt flag */
void efuse_interrupt_flag_clear(efuse_clear_int_flag_enum int_flag);

#endif /* GD32VW55X_EFUSE_H */
