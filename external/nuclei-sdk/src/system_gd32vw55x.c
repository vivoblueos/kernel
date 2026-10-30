/*!
    \file    system_gd32vw55x.c
    \brief   RISC-V Device Peripheral Access Layer Source File for
             GD32VW55x Device Series

    \version 2025-01-16, V1.4.0, firmware for GD32VW55x
*/

/*
 * Copyright (c) 2009-2018 Arm Limited. All rights reserved.
 * Copyright (c) 2019 Nuclei Limited. All rights reserved.
 * Copyright (c) 2025, GigaDevice Semiconductor Inc.
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

/* This file refers the RISC-V standard, some adjustments are made according to GigaDevice chips */

#include "gd32vw55x.h"

/* system frequency define */
#define __IRC16M          (IRC16M_VALUE)            /* internal 16 MHz RC oscillator frequency */
#define __HXTAL           (HXTAL_VALUE)             /* high speed crystal oscillator frequency */
#define __SYS_OSC_CLK     (__IRC16M)                /* main oscillator frequency */

/* select a system clock by uncommenting the following line */
//#define __SYSTEM_CLOCK_IRC16M                       (uint32_t)(__IRC16M)
//#define __SYSTEM_CLOCK_HXTAL                        (uint32_t)(__HXTAL)
//#define __SYSTEM_CLOCK_48M_PLLDIG_IRC16M             (uint32_t)(48000000)
//#define __SYSTEM_CLOCK_160M_PLLDIG_IRC16M             (uint32_t)(160000000)
//#define __SYSTEM_CLOCK_48M_PLLDIG_HXTAL              (uint32_t)(48000000)
#define __SYSTEM_CLOCK_160M_PLLDIG_HXTAL              (uint32_t)(160000000)

#define HXTALSTB_DELAY     {                                 \
                              volatile uint32_t i;           \
                              for(i=0; i<0x2000; i++){       \
                              }                              \
                           }
/* The following is to prevent Vcore fluctuations caused by frequency switching. 
   It is strongly recommended to include it to avoid issues caused by self-removal. */
#define RCU_MODIFY(__delay)     do{                                     \
                                    volatile uint32_t i,reg;            \
                                    if(0 != __delay){                   \
                                        /* Insert a software delay */   \
                                        for(i=0; i<__delay; i++){       \
                                        }                               \
                                        reg = RCU_CFG0;                 \
                                        reg &= ~(RCU_AHB_CKSYS_DIV2);   \
                                        reg |= RCU_AHB_CKSYS_DIV2;      \
                                        /* AHB = SYSCLK/2 */            \
                                        RCU_CFG0 = reg;                 \
                                        /* Insert a software delay */   \
                                        for(i=0; i<__delay; i++){       \
                                        }                               \
                                        reg = RCU_CFG0;                 \
                                        reg &= ~(RCU_AHB_CKSYS_DIV4);   \
                                        reg |= RCU_AHB_CKSYS_DIV4;      \
                                        /* AHB = SYSCLK/4 */            \
                                        RCU_CFG0 = reg;                 \
                                        /* Insert a software delay */   \
                                        for(i=0; i<__delay; i++){       \
                                        }                               \
                                    }                                   \
                                }while(0)

/* set the system clock frequency and declare the system clock configuration function */
#ifdef __SYSTEM_CLOCK_IRC16M
uint32_t SystemCoreClock = __SYSTEM_CLOCK_IRC16M;
static void system_clock_16m_irc16m(void);
#elif defined (__SYSTEM_CLOCK_HXTAL)
uint32_t SystemCoreClock = __SYSTEM_CLOCK_HXTAL;
static void system_clock_hxtal(void);
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_IRC16M)
uint32_t SystemCoreClock = __SYSTEM_CLOCK_48M_PLLDIG_IRC16M;
static void system_clock_48m_irc16m(void);
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_IRC16M)
uint32_t SystemCoreClock = __SYSTEM_CLOCK_160M_PLLDIG_IRC16M;
static void system_clock_160m_irc16m(void);
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_HXTAL)
uint32_t SystemCoreClock = __SYSTEM_CLOCK_48M_PLLDIG_HXTAL;
static void system_clock_48m_hxtal(void);
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_HXTAL)
uint32_t SystemCoreClock = __SYSTEM_CLOCK_160M_PLLDIG_HXTAL;
static void system_clock_160m_hxtal(void);
#endif /* __SYSTEM_CLOCK_IRC16M */

/* configure the system clock */
static void system_clock_config(void);
/* software delay to prevent the impact of Vcore fluctuations.
   It is strongly recommended to include it to avoid issues caused by self-removal. */
static void _soft_delay_(uint32_t time)
{
    __IO uint32_t i;
    for(i=0; i<time*10; i++){
    }
}

/*!
    \brief      setup the microcontroller system, initialize the system
    \param[in]  none
    \param[out] none
    \retval     none
*/
void SystemInit (void)
{
    /* reset the RCU clock configuration to the default reset state */
    /* set IRC16MEN bit */
    RCU_CTL |= RCU_CTL_IRC16MEN;
    while(0U == (RCU_CTL & RCU_CTL_IRC16MSTB)){
    }
    if(((RCU_CFG0 & RCU_CFG0_SCSS) == RCU_SCSS_PLLDIG)){
        RCU_MODIFY(0x50);
    }
    RCU_CFG0 &= ~RCU_CFG0_SCS;
    _soft_delay_(200);
    /* reset CFG0 register */
    RCU_CFG0 = 0x00000000U;

    /* reset HXTALEN, RFCKMEN and PLLEN bits */
    RCU_CTL &= ~(RCU_CTL_PLLDIGEN | RCU_CTL_RFCKMEN | RCU_CTL_HXTALEN);

    /* reset PLLCFGR register */
    RCU_PLL = 0x00000000U;
    RCU_PLLDIGCFG0 = 0x00000000U;
    RCU_PLLDIGCFG1 = 0x07800000U;

    /* disable all interrupts */
    RCU_INT = 0x00000000U;

    /* configure the System clock source, PLL Multiplier and Divider factors,
       AHB/APBx prescalers and Flash settings */
    system_clock_config();
}
/*!
    \brief      configure the system clock
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_config(void)
{
#ifdef __SYSTEM_CLOCK_IRC16M
    system_clock_16m_irc16m();
#elif defined (__SYSTEM_CLOCK_HXTAL)
    system_clock_hxtal();
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_IRC16M)
    system_clock_48m_irc16m();
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_IRC16M)
    system_clock_160m_irc16m();
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_HXTAL)
    system_clock_160m_hxtal();
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_HXTAL)
    system_clock_48m_hxtal();
#endif /* __SYSTEM_CLOCK_IRC16M */
}

#ifdef __SYSTEM_CLOCK_IRC16M
/*!
    \brief      configure the system clock to 16M by IRC16M
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_16m_irc16m(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;

    /* enable IRC16M */
    RCU_CTL |= RCU_CTL_IRC16MEN;

    /* wait until IRC16M is stable or the startup time is longer than IRC16M_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_IRC16MSTB);
    }while((0U == stab_flag) && (IRC16M_STARTUP_TIMEOUT != timeout));

    if(0U == (RCU_CTL & RCU_CTL_IRC16MSTB)){
        /* if fail */
        while(1){
        }
    }

    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV1;

    reg_temp = RCU_CFG0;
    /* select IRC16M as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_IRC16M;
    RCU_CFG0 = reg_temp;

    /* wait until IRC16M is selected as system clock */
    while(RCU_SCSS_IRC16M != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
}

#elif defined (__SYSTEM_CLOCK_HXTAL)
/*!
    \brief      configure the system clock to HXTAL
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_hxtal(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;

    /* power up the HXTAL */
    RCU_CTL |= RCU_CTL_HXTALPU;
    /* enable HXTAL */
    RCU_CTL |= RCU_CTL_HXTALEN;
    HXTALSTB_DELAY
    RCU_CTL |= RCU_CTL_HXTALREADY;
    /* wait until HXTAL is stable or the startup time is longer than HXTAL_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_HXTALSTB);
    }while((0U == stab_flag) && (HXTAL_STARTUP_TIMEOUT != timeout));

    if(0U == (RCU_CTL & RCU_CTL_HXTALSTB)){
        /* if fail */
        while(1){
        }
    }

    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV1;

    reg_temp = RCU_CFG0;
    /* select HXTAL as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_HXTAL;
    RCU_CFG0 = reg_temp;

    /* wait until HXTAL is selected as system clock */
    while(RCU_SCSS_HXTAL != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
}
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_IRC16M)
/*!
    \brief      configure the system clock to 48M by PLL which selects IRC16M as its clock source
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_48m_irc16m(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;

    /* enable IRC16M */
    RCU_CTL |= (RCU_CTL_IRC16MEN | RCU_CTL_IRC16MRFON);

    /* wait until IRC16M is stable or the startup time is longer than IRC16M_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_IRC16MSTB);
    }while((0U == stab_flag) && (IRC16M_STARTUP_TIMEOUT != timeout));

    if(0U == (RCU_CTL & RCU_CTL_IRC16MSTB)){
        /* if fail */
        while(1){
        }
    }

    /* IRC16M is stable */
    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB/1 */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV1;

    RCU_PLL |= RCU_PLLSRC_IRC16M;

    /* 960M = 16MHz*60 */
    RCU_PLLDIGCFG1 = ((960 << 21) / 16) & 0x7FFFFFFF;
    /* PLLDIG OUT = 480M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_480M );
    /* SYS clock = 48M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_SYS_DIV10 );

    /* enable PLLDIG */
    RCU_CFG1 |= (RCU_CFG1_BGPU);
    RCU_CTL |= (RCU_CTL_PLLDIGEN | RCU_CTL_PLLDIGPU);

    /* wait until PLLDIG is stable */
    while(0U == (RCU_CTL & RCU_CTL_PLLDIGSTB)){
    }

    reg_temp = RCU_CFG0;
    /* select PLLDIG as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_PLLDIG;
    RCU_CFG0 = reg_temp;

    /* wait until PLLDIG is selected as system clock */
    while(RCU_SCSS_PLLDIG != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
}
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_IRC16M)
/*!
    \brief      configure the system clock to 160M by PLL which selects IRC16M as its clock source
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_160m_irc16m(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;
	
    /* enable IRC16M */
    RCU_CTL |= (RCU_CTL_IRC16MEN | RCU_CTL_IRC16MRFON);

    /* wait until IRC16M is stable or the startup time is longer than IRC16M_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_IRC16MSTB);
    }while((0U == stab_flag) && (IRC16M_STARTUP_TIMEOUT != timeout));

    /* if fail */
    if(0U == (RCU_CTL & RCU_CTL_IRC16MSTB)){
        while(1){
        }
    }

    /* IRC16M is stable */
    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB/2 */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV2;

    RCU_PLL |= RCU_PLLSRC_IRC16M;

    /* 960M = 16MHz*60 */
    RCU_PLLDIGCFG1 = ((960 << 21) / 16) & 0x7FFFFFFF;
    /* PLLDIG OUT = 480M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_480M );
    /* SYS clock = 160M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_SYS_DIV3 );

    /* enable PLLDIG */
    RCU_CFG1 |= (RCU_CFG1_BGPU);
    RCU_CTL |= (RCU_CTL_PLLDIGEN | RCU_CTL_PLLDIGPU);

    /* wait until PLLDIG is stable */
    while(0U == (RCU_CTL & RCU_CTL_PLLDIGSTB)){
    }

    reg_temp = RCU_CFG0;
    /* select PLLDIG as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_PLLDIG;
    RCU_CFG0 = reg_temp;

    /* wait until PLLDIG is selected as system clock */
    while(RCU_SCSS_PLLDIG != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
}
#elif defined (__SYSTEM_CLOCK_160M_PLLDIG_HXTAL)
/*!
    \brief      configure the system clock to 160M by PLL which selects HXTAL as its clock source
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_160m_hxtal(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;

    /* power up HXTAL */
    RCU_CTL |= RCU_CTL_HXTALPU;
    /* enable HXTAL */
    RCU_CTL |= RCU_CTL_HXTALEN;
    HXTALSTB_DELAY
    RCU_CTL |= RCU_CTL_HXTALREADY;

    /* wait until HXTAL is stable or the startup time is longer than HXTAL_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_HXTALSTB);
    }while((0U == stab_flag) && (HXTAL_STARTUP_TIMEOUT != timeout));

    if(0U == (RCU_CTL & RCU_CTL_HXTALSTB)){
        /* if fail */
        while(1){
        }
    }

    /* HXTAL is stable */
    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB/2 */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV2;

    RCU_PLL |= RCU_PLLSRC_HXTAL;

    /* PLLDIG = 960/HXTAL */
    RCU_PLLDIGCFG1 = ((960 << 21) / (HXTAL_VALUE/1000000)) & 0x7FFFFFFF;

    /* PLLDIG OUT = 480M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_480M );
    /* SYS clock = 160M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_SYS_DIV3 );
    /* enable PLLDIG */
    RCU_CFG1 |= (RCU_CFG1_BGPU);
    RCU_CTL |= (RCU_CTL_PLLDIGEN | RCU_CTL_PLLDIGPU);
    /* wait until PLLDIG is stable */
    while(0U == (RCU_CTL & RCU_CTL_PLLDIGSTB)){
    }
    reg_temp = RCU_CFG0;
    /* select PLLDIG as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_PLLDIG;
    RCU_CFG0 = reg_temp;

    /* wait until PLLDIG is selected as system clock */
    while(RCU_SCSS_PLLDIG != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
} /* __SYSTEM_CLOCK_IRC16M */
#elif defined (__SYSTEM_CLOCK_48M_PLLDIG_HXTAL)
/*!
    \brief      configure the system clock to 48M by PLL which selects HXTAL as its clock source
    \param[in]  none
    \param[out] none
    \retval     none
*/
static void system_clock_48m_hxtal(void)
{
    uint32_t timeout = 0U;
    uint32_t stab_flag = 0U;
    __IO uint32_t reg_temp;

    /* power up HXTAL */
    RCU_CTL |= RCU_CTL_HXTALPU;
    /* enable HXTAL */
    RCU_CTL |= RCU_CTL_HXTALEN;
    HXTALSTB_DELAY
    RCU_CTL |= RCU_CTL_HXTALREADY;

    /* wait until HXTAL is stable or the startup time is longer than HXTAL_STARTUP_TIMEOUT */
    do{
        timeout++;
        stab_flag = (RCU_CTL & RCU_CTL_HXTALSTB);
    }while((0U == stab_flag) && (HXTAL_STARTUP_TIMEOUT != timeout));

    if(0U == (RCU_CTL & RCU_CTL_HXTALSTB)){
        /* if fail */
        while(1){
        }
    }

    /* HXTAL is stable */
    /* AHB = SYSCLK */
    RCU_CFG0 |= RCU_AHB_CKSYS_DIV1;
    /* APB2 = AHB */
    RCU_CFG0 |= RCU_APB2_CKAHB_DIV1;
    /* APB1 = AHB/2 */
    RCU_CFG0 |= RCU_APB1_CKAHB_DIV2;

    RCU_PLL |= RCU_PLLSRC_HXTAL;

    /* PLLDIG = 960/HXTAL */
    RCU_PLLDIGCFG1 = ((960 << 21) / (HXTAL_VALUE/1000000)) & 0x7FFFFFFF;

    /* PLLDIG OUT = 480M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_480M );
    /* SYS clock = 48M */
    RCU_PLLDIGCFG0 |= ( RCU_PLLDIG_SYS_DIV10 );
    /* enable PLL */
    RCU_CFG1 |= (RCU_CFG1_BGPU);
    RCU_CTL |= (RCU_CTL_PLLDIGEN | RCU_CTL_PLLDIGPU);
    /* wait until PLL is stable */
    while(0U == (RCU_CTL & RCU_CTL_PLLDIGSTB)){
    }

    reg_temp = RCU_CFG0;
    /* select PLL as system clock */
    reg_temp &= ~RCU_CFG0_SCS;
    reg_temp |= RCU_CKSYSSRC_PLLDIG;
    RCU_CFG0 = reg_temp;

    /* wait until PLL is selected as system clock */
    while(RCU_SCSS_PLLDIG != (RCU_CFG0 & RCU_CFG0_SCSS)){
    }
}
#endif

/*!
    \brief      update the SystemCoreClock with current core clock retrieved from cpu registers
    \param[in]  none
    \param[out] none
    \retval     none
*/
void SystemCoreClockUpdate (void)
{
    uint32_t sws;
    uint32_t fresel, plldigdiv, outputfre, idx, clk_exp;

    /* exponent of AHB, APB1 and APB2 clock divider */
    const uint8_t ahb_exp[16] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 7, 8, 9};

    sws = GET_BITS(RCU_CFG0, 2, 3);
    switch(sws){
    /* IRC16M is selected as CK_SYS */
    case 0:
        SystemCoreClock = IRC16M_VALUE;
        break;
    /* HXTAL is selected as CK_SYS */
    case 1:
        SystemCoreClock = HXTAL_VALUE;
        break;
    /* PLLDIG is selected as CK_SYS */
    case 2:
        /* get the value of PLLDIGOSEL[1:0] */
        fresel = GET_BITS(RCU_PLLDIGCFG0, 24U, 25U);
        switch(fresel){
        case 0:
            outputfre = 192000000;
            break;
        case 1:
            outputfre = 240000000;
            break;
        case 2:
            outputfre = 320000000;
            break;
        case 3:
            outputfre = 480000000;
            break;
        default:
            outputfre = 192000000;
            break;
        }
        plldigdiv = (GET_BITS(RCU_PLLDIGCFG0, 26U, 31U) + 1U);
        SystemCoreClock = outputfre/plldigdiv;
        break;
    /* IRC16M is selected as CK_SYS */
    default:
        SystemCoreClock = IRC16M_VALUE;
        break;
    }
    /* calculate AHB clock frequency */
    idx = GET_BITS(RCU_CFG0, 4, 7);
    clk_exp = ahb_exp[idx];
    SystemCoreClock = SystemCoreClock >> clk_exp;
}


#ifdef __FIRMWARE_VERSION_DEFINE
/*!
    \brief      get firmware version
    \param[in]  none
    \param[out] none
    \retval     firmware version
*/
uint32_t gd32vw55x_firmware_version_get(void)
{
    return __GD32VW55X_STDPERIPH_VERSION;
}
#endif /* __FIRMWARE_VERSION_DEFINE */
