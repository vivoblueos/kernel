/*!
    \file    gd32vw55x_syscfg.h
    \brief   definitions for the SYSCFG

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

#ifndef GD32VW55X_SYSCFG_H
#define GD32VW55X_SYSCFG_H

#include "gd32vw55x.h"

#define SYSCFG                                  SYSCFG_BASE                                       /*!< SYSCFG base address */

/* registers definitions */
#define SYSCFG_CFG0                             REG32(SYSCFG + 0x00000000U)                       /*!< SYSCFG configuration register 0 */
#define SYSCFG_EXTISS0                          REG32(SYSCFG + 0x00000008U)                       /*!< EXTI sources selection register 0 */
#define SYSCFG_EXTISS1                          REG32(SYSCFG + 0x0000000CU)                       /*!< EXTI sources selection register 1 */
#define SYSCFG_EXTISS2                          REG32(SYSCFG + 0x00000010U)                       /*!< EXTI sources selection register 2 */
#define SYSCFG_EXTISS3                          REG32(SYSCFG + 0x00000014U)                       /*!< EXTI sources selection register 3 */
#define SYSCFG_CPSCTL                           REG32(SYSCFG + 0x00000020U)                       /*!< I/O compensation control register */
#define SYSCFG_CFG1                             REG32(SYSCFG + 0x00000054U)                       /*!< SYSCFG configuration register 1 */
#define SYSCFG_SCFG                             REG32(SYSCFG + 0x00000068U)                       /*!< SYSCFG shared SRAM configuration register */
#define SYSCFG_TIMER0CFG                        REG32(SYSCFG + 0x00000100U)                       /*!< Timer0 controls the register from slave model */
#define SYSCFG_TIMER1CFG                        REG32(SYSCFG + 0x00000104U)                       /*!< Timer1 controls the register from slave model */
#define SYSCFG_TIMER2CFG                        REG32(SYSCFG + 0x00000108U)                       /*!< Timer2 controls the register from slave model */

/* bits definitions */
/* SYSCFG_CFG0 */
#define SYSCFG_CFG0_BOOT_MODE                   BITS(0,1)                                         /*!< Boot mode */

/* SYSCFG_EXTISS0 bits definitions */
#define SYSCFG_EXTISS0_EXTI0_SS                 BITS(0,3)                                         /*!< EXTI 0 source selection */
#define SYSCFG_EXTISS0_EXTI1_SS                 BITS(4,7)                                         /*!< EXTI 1 source selection */
#define SYSCFG_EXTISS0_EXTI2_SS                 BITS(8,11)                                        /*!< EXTI 2 source selection */
#define SYSCFG_EXTISS0_EXTI3_SS                 BITS(12,15)                                       /*!< EXTI 3 source selection */

/* SYSCFG_EXTISS1 bits definitions */
#define SYSCFG_EXTISS1_EXTI4_SS                 BITS(0,3)                                         /*!< EXTI 4 source selection */
#define SYSCFG_EXTISS1_EXTI5_SS                 BITS(4,7)                                         /*!< EXTI 5 source selection */
#define SYSCFG_EXTISS1_EXTI6_SS                 BITS(8,11)                                        /*!< EXTI 6 source selection */
#define SYSCFG_EXTISS1_EXTI7_SS                 BITS(12,15)                                       /*!< EXTI 7 source selection */

/* SYSCFG_EXTISS2 bits definitions */
#define SYSCFG_EXTISS2_EXTI8_SS                 BITS(0,3)                                         /*!< EXTI 8 source selection */
#define SYSCFG_EXTISS2_EXTI9_SS                 BITS(4,7)                                         /*!< EXTI 9 source selection */
#define SYSCFG_EXTISS2_EXTI10_SS                BITS(8,11)                                        /*!< EXTI 10 source selection */
#define SYSCFG_EXTISS2_EXTI11_SS                BITS(12,15)                                       /*!< EXTI 11 source selection */

/* SYSCFG_EXTISS3 bits definitions */
#define SYSCFG_EXTISS3_EXTI12_SS                BITS(0,3)                                         /*!< EXTI 12 source selection */
#define SYSCFG_EXTISS3_EXTI13_SS                BITS(4,7)                                         /*!< EXTI 13 source selection */
#define SYSCFG_EXTISS3_EXTI14_SS                BITS(8,11)                                        /*!< EXTI 14 source selection */
#define SYSCFG_EXTISS3_EXTI15_SS                BITS(12,15)                                       /*!< EXTI 15 source selection */

/* SYSCFG_CPSCTL bits definitions */
#define SYSCFG_CPSCTL_CPS_EN                    BIT(0)                                            /*!< Compensation cell power-down */
#define SYSCFG_CPSCTL_CPS_RDY                   BIT(8)                                            /*!< Compensation cell ready flag */

/* SYSCFG_CFG1 bits definitions */
#define SYSCFG_CFG1_LVD_LOCK                    BIT(2)                                            /*!< LVD lock enable bit */

/* SYSCFG_SCFG bits definitions */
#define SYSCFG_SCFG_SOWNSEL                     BIT(0)                                            /*!< control the ownership of the shared 32K SRAM */

/* SYSCFG_TIMERxCFG,x=0..2 bits definitions */
#define SYSCFG_TIMERxCFG_TSCFG0                 BITS(0,3)                                         /*!< Quadrature decoder mode 0 */
#define SYSCFG_TIMERxCFG_TSCFG1                 BITS(4,7)                                         /*!< Quadrature decoder mode 1 */
#define SYSCFG_TIMERxCFG_TSCFG2                 BITS(8,11)                                        /*!< Quadrature decoder mode 2 */
#define SYSCFG_TIMERxCFG_TSCFG3                 BITS(12,15)                                       /*!< restart model */
#define SYSCFG_TIMERxCFG_TSCFG4                 BITS(16,19)                                       /*!< pause model */
#define SYSCFG_TIMERxCFG_TSCFG5                 BITS(20,23)                                       /*!< event model */
#define SYSCFG_TIMERxCFG_TSCFG6                 BITS(24,27)                                       /*!< external clock model */
#define SYSCFG_TIMERxCFG_TSCFG7                 BITS(28,31)                                       /*!< slave mode disable */

/* constants definitions */
/* timer tigger source select definition */
#define TIMER_SMCFG_TRGSEL_NONE                 ((uint8_t)0x00U)                                  /*!< internal trigger 0 */
#define TIMER_SMCFG_TRGSEL_ITI0                 ((uint8_t)0x01U)                                  /*!< internal trigger 0 */
#define TIMER_SMCFG_TRGSEL_ITI1                 ((uint8_t)0x02U)                                  /*!< internal trigger 1 */
#define TIMER_SMCFG_TRGSEL_ITI2                 ((uint8_t)0x03U)                                  /*!< internal trigger 2 */
#define TIMER_SMCFG_TRGSEL_ITI3                 ((uint8_t)0x04U)                                  /*!< internal trigger 3 */
#define TIMER_SMCFG_TRGSEL_CI0F_ED              ((uint8_t)0x05U)                                  /*!< TI0 Edge Detector */
#define TIMER_SMCFG_TRGSEL_CI0FE0               ((uint8_t)0x06U)                                  /*!< filtered TIMER input 0 */
#define TIMER_SMCFG_TRGSEL_CI1FE1               ((uint8_t)0x07U)                                  /*!< filtered TIMER input 1 */
#define TIMER_SMCFG_TRGSEL_ETIFP                ((uint8_t)0x08U)                                  /*!< external trigger */

/* timer tigger mode select definition */
#define TIMER_QUAD_DECODER_MODE0            ((uint8_t)0x00U)                                      /*!< quadrature decoder mode 0 */
#define TIMER_QUAD_DECODER_MODE1            ((uint8_t)0x01U)                                      /*!< quadrature decoder mode 1 */
#define TIMER_QUAD_DECODER_MODE2            ((uint8_t)0x02U)                                      /*!< quadrature decoder mode 2 */
#define TIMER_SLAVE_MODE_RESTART            ((uint8_t)0x03U)                                      /*!< restart mode */
#define TIMER_SLAVE_MODE_PAUSE              ((uint8_t)0x04U)                                      /*!< pause mode */
#define TIMER_SLAVE_MODE_EVENT              ((uint8_t)0x05U)                                      /*!< event mode */
#define TIMER_SLAVE_MODE_EXTERNAL0          ((uint8_t)0x06U)                                      /*!< external clock mode 0 */
#define TIMER_SLAVE_MODE_DISABLE            ((uint8_t)0x07U)                                      /*!< slave mode disable */

/* code start mode enum definition */
typedef enum {
    FLASH_START = 0U,                                                                             /*!< flash start mode */
    SRAM_START,                                                                                   /*!< sram start mode */
    SYSTEM_START                                                                                  /*!< system start mode */
} syscfg_code_start_enum;

/* EXTI source select definition */
#define EXTISS0                                 ((uint8_t)0x00U)                                  /*!< EXTI source select register 0 */
#define EXTISS1                                 ((uint8_t)0x01U)                                  /*!< EXTI source select register 1 */
#define EXTISS2                                 ((uint8_t)0x02U)                                  /*!< EXTI source select register 2 */
#define EXTISS3                                 ((uint8_t)0x03U)                                  /*!< EXTI source select register 3 */

/* EXTI source select mask bits definition */
#define EXTI_SS_MASK                            BITS(0,3)                                         /*!< EXTI source select mask */

/* EXTI source select jumping step definition */
#define EXTI_SS_JSTEP                           ((uint8_t)(0x04U))                                /*!< EXTI source select jumping step */

/* EXTI source select moving step definition */
#define EXTI_SS_MSTEP(pin)                      (EXTI_SS_JSTEP * ((pin) % EXTI_SS_JSTEP))         /*!< EXTI source select moving step */

/* EXTI source port definitions */
#define EXTI_SOURCE_GPIOA                       ((uint8_t)0x00U)                                  /*!< EXTI GPIOA configuration */
#define EXTI_SOURCE_GPIOB                       ((uint8_t)0x01U)                                  /*!< EXTI GPIOB configuration */
#define EXTI_SOURCE_GPIOC                       ((uint8_t)0x02U)                                  /*!< EXTI GPIOC configuration */

/* EXTI source pin definitions */
#define EXTI_SOURCE_PIN0                        ((uint8_t)0x00U)                                  /*!< EXTI GPIO pin0 configuration */
#define EXTI_SOURCE_PIN1                        ((uint8_t)0x01U)                                  /*!< EXTI GPIO pin1 configuration */
#define EXTI_SOURCE_PIN2                        ((uint8_t)0x02U)                                  /*!< EXTI GPIO pin2 configuration */
#define EXTI_SOURCE_PIN3                        ((uint8_t)0x03U)                                  /*!< EXTI GPIO pin3 configuration */
#define EXTI_SOURCE_PIN4                        ((uint8_t)0x04U)                                  /*!< EXTI GPIO pin4 configuration */
#define EXTI_SOURCE_PIN5                        ((uint8_t)0x05U)                                  /*!< EXTI GPIO pin5 configuration */
#define EXTI_SOURCE_PIN6                        ((uint8_t)0x06U)                                  /*!< EXTI GPIO pin6 configuration */
#define EXTI_SOURCE_PIN7                        ((uint8_t)0x07U)                                  /*!< EXTI GPIO pin7 configuration */
#define EXTI_SOURCE_PIN8                        ((uint8_t)0x08U)                                  /*!< EXTI GPIO pin8 configuration */
#define EXTI_SOURCE_PIN9                        ((uint8_t)0x09U)                                  /*!< EXTI GPIO pin9 configuration */
#define EXTI_SOURCE_PIN10                       ((uint8_t)0x0AU)                                  /*!< EXTI GPIO pin10 configuration */
#define EXTI_SOURCE_PIN11                       ((uint8_t)0x0BU)                                  /*!< EXTI GPIO pin11 configuration */
#define EXTI_SOURCE_PIN12                       ((uint8_t)0x0CU)                                  /*!< EXTI GPIO pin12 configuration */
#define EXTI_SOURCE_PIN13                       ((uint8_t)0x0DU)                                  /*!< EXTI GPIO pin13 configuration */
#define EXTI_SOURCE_PIN14                       ((uint8_t)0x0EU)                                  /*!< EXTI GPIO pin14 configuration */
#define EXTI_SOURCE_PIN15                       ((uint8_t)0x0FU)                                  /*!< EXTI GPIO pin15 configuration */

/* lock definitions */
#define SYSCFG_LOCK_LVD                         SYSCFG_CFG1_LVD_LOCK                              /*!< LVD lock */

/* The ownership of the SRAM definitions */
#define SRAM_OWN(regval)                        (BIT(0) & ((uint32_t)(regval) << 0u))
#define SRAMEN_WIRELESS                         SRAM_OWN(0)                                       /*!< The ownership of the share sram is wireless */
#define SRAMEN_CORE                             SRAM_OWN(1)                                       /*!< The ownership of the share sram is core */

/* function declarations */
/* initialization functions */
/* reset the SYSCFG registers */
void syscfg_deinit(void);
/* function configuration */
/* configure the GPIO pin as EXTI Line */
void syscfg_exti_line_config(uint8_t exti_port, uint8_t exti_pin);
/* enable I/O compensation cell */
void syscfg_io_compensation_enable(void);
/* disable I/O compensation cell */
void syscfg_io_compensation_disable(void);
/* connect TIMER0/15/16 break input to the selected parameter */
void syscfg_lock_config(void);
/* get the compensation ready flag */
FlagStatus syscfg_io_compensation_ready_flag_get(void);
/* configure the ownership of the shared 32k SRAM */
void syscfg_sram_ownership_config(uint32_t sram_owner);
/* get code start mode */
syscfg_code_start_enum syscfg_boot_mode_get(void);

#endif /* GD32VW55X_SYSCFG_H */
