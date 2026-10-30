/*!
    \file    gd32vw55x_dbg.h
    \brief   definitions for the DBG

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

#ifndef GD32VW55X_DBG_H
#define GD32VW55X_DBG_H

#include "gd32vw55x.h"

/* DBG definitions */
#define DBG                      DBG_BASE                      /*!< DBG base address */

/* registers definitions */
#define DBG_ID                   REG32(DBG + 0x00000000U)      /*!< DBG_ID code register */
#define DBG_CTL0                 REG32(DBG + 0x00000004U)      /*!< DBG control register 0 */
#define DBG_CTL1                 REG32(DBG + 0x00000008U)      /*!< DBG control register 1 */
#define DBG_CTL2                 REG32(DBG + 0x0000000CU)      /*!< DBG control register 2 */

/* bits definitions */
/* DBG_ID */
#define DBG_ID_ID_CODE           BITS(0,31)                    /*!< DBG ID code values */

/* DBG_CTL0 */
#define DBG_CTL0_SLP_HOLD        BIT(0)                        /*!< keep debugger connection during sleep mode */
#define DBG_CTL0_DSLP_HOLD       BIT(1)                        /*!< keep debugger connection during deepsleep mode */
#define DBG_CTL0_STB_HOLD        BIT(2)                        /*!< keep debugger connection during standby mode */

/* DBG_CTL1 */
#define DBG_CTL1_TIMER1_HOLD     BIT(0)                        /*!< hold TIMER1 counter when core is halted */
#define DBG_CTL1_TIMER2_HOLD     BIT(1)                        /*!< hold TIMER2 counter when core is halted */
#define DBG_CTL1_TIMER5_HOLD     BIT(4)                        /*!< hold TIMER5 counter when core is halted */
#define DBG_CTL1_RTC_HOLD        BIT(10)                       /*!< hold RTC calendar and wakeup counter when core is halted */
#define DBG_CTL1_WWDGT_HOLD      BIT(11)                       /*!< debug WWDGT kept when core is halted */
#define DBG_CTL1_FWDGT_HOLD      BIT(12)                       /*!< debug FWDGT kept when core is halted */
#define DBG_CTL1_I2C0_HOLD       BIT(21)                       /*!< hold I2C0 smbus when core is halted */
#define DBG_CTL1_I2C1_HOLD       BIT(22)                       /*!< hold I2C1 smbus when core is halted */

/* DBG_CTL2 */
#define DBG_CTL2_TIMER0_HOLD     BIT(0)                        /*!< hold TIMER0 counter when core is halted */
#define DBG_CTL2_TIMER15_HOLD    BIT(23)                       /*!< hold TIMER15 counter when core is halted */
#define DBG_CTL2_TIMER16_HOLD    BIT(24)                       /*!< hold TIMER16 counter when core is halted */

/* constants definitions */
/* keep debugger connection */
#define DBG_LOW_POWER_SLEEP      DBG_CTL0_SLP_HOLD             /*!< keep debugger connection during sleep mode */
#define DBG_LOW_POWER_DEEPSLEEP  DBG_CTL0_DSLP_HOLD            /*!< keep debugger connection during deepsleep mode */
#define DBG_LOW_POWER_STANDBY    DBG_CTL0_STB_HOLD             /*!< keep debugger connection during standby mode */

typedef enum {
    DBG_TIMER1_HOLD            = BIT(0),                       /*!< hold TIMER1 counter when core is halted */
    DBG_TIMER2_HOLD            = BIT(1),                       /*!< hold TIMER2 counter when core is halted */
    DBG_TIMER5_HOLD            = BIT(4),                       /*!< hold TIMER5 counter when core is halted */
    DBG_RTC_HOLD               = BIT(10),                      /*!< hold RTC calendar and wakeup counter when core is halted */
    DBG_WWDGT_HOLD             = BIT(11),                      /*!< debug WWDGT kept when core is halted */
    DBG_FWDGT_HOLD             = BIT(12),                      /*!< debug FWDGT kept when core is halted */
    DBG_I2C0_HOLD              = BIT(21),                      /*!< hold I2C0 smbus when core is halted */
    DBG_I2C1_HOLD              = BIT(22),                      /*!< hold I2C1 smbus when core is halted */
    DBG_TIMER0_HOLD            = (BIT(0) | BIT(30)),           /*!< hold TIMER0 counter when core is halted */
    DBG_TIMER15_HOLD           = (BIT(23) | BIT(30)),          /*!< hold TIMER15 counter when core is halted */
    DBG_TIMER16_HOLD           = (BIT(24) | BIT(30)),          /*!< hold TIMER16 counter when core is halted */
} dbg_periph_enum;

/* function declarations */
/* deinitialize the DBG */
void dbg_deinit(void);
/* read DBG_ID code register */
uint32_t dbg_id_get(void);

/* enable low power behavior when the MCU is in debug mode */
void dbg_low_power_enable(uint32_t dbg_low_power);
/* disable low power behavior when the MCU is in debug mode */
void dbg_low_power_disable(uint32_t dbg_low_power);

/* enable peripheral behavior when the MCU is in debug mode */
void dbg_periph_enable(dbg_periph_enum dbg_periph);
/* disable peripheral behavior when the MCU is in debug mode */
void dbg_periph_disable(dbg_periph_enum dbg_periph);

#endif /* GD32VW55X_DBG_H */
