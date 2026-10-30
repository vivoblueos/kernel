/*!
    \file    gd32vw55x.h
    \brief   general definitions for GD32VW55x

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

#ifndef GD32VW55x_H
#define GD32VW55x_H

#include <stddef.h>
#include <stdio.h>

#ifdef __cplusplus
 extern "C" {
#endif

/* SoC Download mode definition */
#define DOWNLOAD_MODE_FLASHXIP      0   /*!< flashxip download mode */
#define DOWNLOAD_MODE_FLASH         1   /*!< flash download mode */
#define DOWNLOAD_MODE_ILM           2   /*!< ilm download mode */
#define DOWNLOAD_MODE_SRAM          3   /*!< sram download mode */
#define DOWNLOAD_MODE_MAX           4

 /* IO definitions (access restrictions to peripheral registers) */
 /**
     <strong>IO Type Qualifiers</strong> are used
     \li to specify the access to peripheral variables.
     \li for automatic generation of peripheral register debug information.
 */
#ifdef __cplusplus
#define   __I     volatile             /*!< Defines 'read only' permissions                 */
#else
#define   __I     volatile const       /*!< Defines 'read only' permissions                 */
#endif
#define   __O     volatile             /*!< Defines 'write only' permissions                */
#define   __IO    volatile             /*!< Defines 'read / write' permissions              */

/* define value of high speed crystal oscillator (HXTAL) in Hz */
#if !defined  (HXTAL_VALUE)
#define HXTAL_VALUE  ((uint32_t)40000000)
#endif /* high speed crystal oscillator value */

/* define startup timeout value of high speed crystal oscillator (HXTAL) */
#if !defined  (HXTAL_STARTUP_TIMEOUT)
#define HXTAL_STARTUP_TIMEOUT   ((uint16_t)0xFFFFU)
#endif /* high speed crystal oscillator startup timeout */

/* define value of internal 16MHz RC oscillator (IRC16M) in Hz */
#if !defined  (IRC16M_VALUE)
#define IRC16M_VALUE  ((uint32_t)16000000)
#endif /* internal 16MHz RC oscillator value */

/* define startup timeout value of internal 16MHz RC oscillator (IRC16M) */
#if !defined  (IRC16M_STARTUP_TIMEOUT)
#define IRC16M_STARTUP_TIMEOUT   ((uint16_t)0x0500U)
#endif /* internal 16MHz RC oscillator startup timeout */

/* define value of internal 32KHz RC oscillator(IRC32K) in Hz */
#if !defined  (IRC32K_VALUE)
#define IRC32K_VALUE  ((uint32_t)32000)
#endif /* internal 32KHz RC oscillator value */

/* define value of low speed crystal oscillator (LXTAL)in Hz */
#if !defined  (LXTAL_VALUE)
#define LXTAL_VALUE  ((uint32_t)32768)
#endif /* low speed crystal oscillator value */

/* GD32VW55x firmware library version number V1.0 */
#define __GD32VW55X_STDPERIPH_VERSION_MAIN   (0x01) /*!< [31:24] main version */
#define __GD32VW55X_STDPERIPH_VERSION_SUB1   (0x00) /*!< [23:16] sub1 version */
#define __GD32VW55X_STDPERIPH_VERSION_SUB2   (0x00) /*!< [15:8]  sub2 version */
#define __GD32VW55X_STDPERIPH_VERSION_RC     (0x00) /*!< [7:0]  release candidate */
#define __GD32VW55X_STDPERIPH_VERSION        ((__GD32VW55X_STDPERIPH_VERSION_MAIN << 24)\
                                            |(__GD32VW55X_STDPERIPH_VERSION_SUB1 << 16)\
                                            |(__GD32VW55X_STDPERIPH_VERSION_SUB2 << 8)\
                                            |(__GD32VW55X_STDPERIPH_VERSION_RC))

/* define the correct core features for the GD32VW55x */
#define __ECLIC_PRESENT           1                     /*!< Set to 1 if ECLIC is present */

#ifndef __ECLIC_RAM_VECTOR
#define __ECLIC_RAM_VECTOR        0                     /*!< TODO: not yet supported, set to 1 if you want your vector table located in RAM*/
#endif

#define __ECLIC_BASEADDR          0xD2000000UL          /*!< Set to ECLIC baseaddr */

#define __ECLIC_INTCTLBITS        4                     /*!< Set to 1 - 8, the number of hardware bits are actually implemented in the clicintctl registers. */
#define __ECLIC_INTNUM            SOC_INT_MAX           /*!< Set to 1 - 1024, total interrupt number of ECLIC Unit */
#define __SYSTIMER_PRESENT        1                     /*!< Set to 1 if System Timer is present */
#define __SYSTIMER_BASEADDR       0xD1000000UL          /*!< Set to SysTimer baseaddr */

/*!< Set to 0, 1, or 2, 0 not present, 1 single floating point unit present, 2 double floating point unit present */
#if !defined(__riscv_flen)
#define __FPU_PRESENT             0
#elif __riscv_flen == 32
#define __FPU_PRESENT             1
#else
#define __FPU_PRESENT             2
#endif

#if defined(__riscv_bitmanip)
#define __BITMANIP_PRESENT        1                     /*!< Set to 1 if Bitmainpulation extension is present */
#else
#define __BITMANIP_PRESENT        0                     /*!< Set to 1 if Bitmainpulation extension is present */
#endif
#if defined(__riscv_dsp)
#define __DSP_PRESENT             1                     /*!< Set to 1 if Partial SIMD(DSP) extension is present */
#else
#define __DSP_PRESENT             0                     /*!< Set to 1 if Partial SIMD(DSP) extension is present */
#endif

#define __PMP_PRESENT             1                     /*!< Set to 1 if PMP is present */
#define __PMP_ENTRY_NUM           8                     /*!< Set to 8 or 16, the number of PMP entries */
#define __ICACHE_PRESENT          1                     /*!< Set to 1 if I-Cache is present */
#define __DCACHE_PRESENT          0                     /*!< Set to 1 if D-Cache is present */
#define __Vendor_SysTickConfig    0                     /*!< Set to 1 if different SysTick Config is used */
#define __Vendor_EXCEPTION        0                     /*!< Set to 1 if vendor exception hander is present */


/* define interrupt number */
typedef enum IRQn
{
    CLIC_INT_SFT                = 3,      /*!< CPU Software interrupt */
    SysTimerSW_IRQn             = 3,      /*!< CPU Software interrupt */
    CLIC_INT_TMR                = 7,      /*!< CPU Timer interrupt */
    SysTimer_IRQn               = 7,      /*!< CPU Timer Interrupt */

    /* interruput numbers */
    WWDGT_IRQn                  = 19,     /*!< window watchdog timer interrupt */
    LVD_IRQn                    = 20,     /*!< LVD through EXTI line detect interrupt */
    TAMPER_STAMP_IRQn           = 21,     /*!< tamper and timestamp through EXTI line detect */
    RTC_WKUP_IRQn               = 22,     /*!< RTC wakeup through EXTI line interrupt */
    FMC_IRQn                    = 23,     /*!< FMC interrupt */
    RCU_IRQn                    = 24,     /*!< RCU interrupt */
    EXTI0_IRQn                  = 25,     /*!< EXTI line 0 interrupts */
    EXTI1_IRQn                  = 26,     /*!< EXTI line 1 interrupts */
    EXTI2_IRQn                  = 27,     /*!< EXTI line 2 interrupts */
    EXTI3_IRQn                  = 28,     /*!< EXTI line 3 interrupts */
    EXTI4_IRQn                  = 29,     /*!< EXTI line 4 interrupts */
    DMA_Channel0_IRQn           = 30,     /*!< DMA channel0 Interrupt */
    DMA_Channel1_IRQn           = 31,     /*!< DMA channel1 Interrupt */
    DMA_Channel2_IRQn           = 32,     /*!< DMA channel2 interrupt */
    DMA_Channel3_IRQn           = 33,     /*!< DMA channel3 interrupt */
    DMA_Channel4_IRQn           = 34,     /*!< DMA channel4 interrupt */
    DMA_Channel5_IRQn           = 35,     /*!< DMA channel5 interrupt */
    DMA_Channel6_IRQn           = 36,     /*!< DMA channel6 interrupt */
    DMA_Channel7_IRQn           = 37,     /*!< DMA channel7 interrupt */
    ADC_IRQn                    = 38,     /*!< ADC interrupt */
    EXTI5_9_IRQn                = 42,     /*!< EXTI[9:5] interrupts */
    TIMER0_BRK_IRQn             = 43,     /*!< TIMER0 break interrupts */
    TIMER0_UP_IRQn              = 44,     /*!< TIMER0 update interrupts */
    TIMER0_CMT_IRQn             = 45,     /*!< TIMER0 commutation interrupts */
    TIMER0_Channel_IRQn         = 46,     /*!< TIMER0 channel capture compare interrupt */
    TIMER1_IRQn                 = 47,     /*!< TIMER1 interrupt */
    TIMER2_IRQn                 = 48,     /*!< TIMER2 interrupt */
    I2C0_EV_IRQn                = 50,     /*!< I2C0 event interrupt */
    I2C0_ER_IRQn                = 51,     /*!< I2C0 error interrupt */
    I2C1_EV_IRQn                = 52,     /*!< I2C1 event interrupt */
    I2C1_ER_IRQn                = 53,     /*!< I2C1 error interrupt */
    SPI_IRQn                    = 54,     /*!< SPI interrupt */
    USART0_IRQn                 = 56,     /*!< USART0 interrupt */
    UART1_IRQn                  = 57,     /*!< UART1 interrupt */
    UART2_IRQn                  = 58,     /*!< UART2 interrupt */
    EXTI10_15_IRQn              = 59,     /*!< EXTI[15:10] interrupts */
    RTC_Alarm_IRQn              = 60,     /*!< RTC alarm interrupt */
    VLVDF_IRQn                  = 61,     /*!< VLVDF interrupt */
    TIMER15_IRQn                = 63,     /*!< TIMER15 global interrupt */
    TIMER16_IRQn                = 64,     /*!< TIMER16 global interrupt */
    I2C0_WKUP_IRQn              = 70,     /*!< I2C0 Wakeup interrupt*/
    USART0_WKUP_IRQn            = 71,     /*!< USART0 Wakeup */
    TIMER5_IRQn                 = 73,     /*!< TIMER5 global interrupt */
    WIFI_TRIGGER_IRQn           = 74,     /*!< WIFI Protocol trigger interrupt */
    WIFI_MAC_IRQn               = 75,     /*!< WIFI MAC interrupt */
    WIFI_TX_IRQn                = 76,     /*!< WIFI Tx interrupt */
    WIFI_RX_IRQn                = 77,     /*!< WIFI Rx interrupt */
    LA_IRQn                     = 83,     /*!< LA interrupt */
    WIFI_WKUP_IRQn              = 84,     /*!< WIFI wakeup */
    BLE_WKUP_IRQn               = 85,     /*!< BLE wakeup */
    PLATFORM_WAKE_IRQn          = 86,     /*!< Platform wake interrupt */
    ISO_BT_STAMP0_IRQn          = 87,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP1_IRQn          = 88,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP2_IRQn          = 89,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP3_IRQn          = 90,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP4_IRQn          = 91,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP5_IRQn          = 92,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP6_IRQn          = 93,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    ISO_BT_STAMP7_IRQn          = 94,     /*!< ISO Bluetooth TimeStamp interrupt0 */
    PMU_IRQn                    = 95,     /*!< PMU interrupt */
    CAU_IRQn                    = 98,     /*!< CAU interrupt */
    HAU_TRNG_IRQn               = 99,     /*!< HAU and TRNG interrupt */
    WIFI_INT_IRQn               = 101,    /*!< WIFI global interrupt */
    WIFI_SW_TRIG_IRQn           = 102,    /*!< SW triggered interrupt */
    WIFI_FINE_TIMER_TARGET_IRQn = 103,    /*!< Fine Timer Target interrupt */
    WIFI_STAMP_TARGET1_IRQn     = 104,    /*!< Timestamp Target 1 interrupt */
    WIFI_STAMP_TARGET2_IRQn     = 105,    /*!< Timestamp Target 2 interrupt */
    WIFI_STAMP_TARGET3_IRQn     = 106,    /*!< Timestamp Target 3 interrupt */
    WIFI_ENCRYPTION_ENGINE_IRQn = 107,    /*!< Encryption engine interrupt */
    WIFI_SLEEP_MODE_IRQn        = 108,    /*!< Sleep Mode interrupt */
    WIFI_HALF_SLOT_IRQn         = 109,    /*!< Half Slot interrupt */
    WIFI_FIFO_ACTIVITY_IRQn     = 110,    /*!< FIFO Activity interrupt */
    WIFI_ERROR_IRQn             = 111,    /*!< Error interrupt */
    WIFI_FREQ_SELECT_IRQn       = 112,    /*!< Frequency Selection interrupt */
    EFUSE_IRQn                  = 113,    /*!< EFUSE global interrupt */
    QSPI_IRQn                   = 114,    /*!< QSPI global interrupt */
    PKCAU_IRQn                  = 115,    /*!< PKCAU global interrupt */
    SOC_INT_MAX
} IRQn_Type;

typedef enum EXCn {
    /* =======================================  Nuclei N/NX Specific Exception Code  ======================================== */
    InsUnalign_EXCn          =   0,              /*!<  Instruction address misaligned */
    InsAccFault_EXCn         =   1,              /*!<  Instruction access fault */
    IlleIns_EXCn             =   2,              /*!<  Illegal instruction */
    Break_EXCn               =   3,              /*!<  Beakpoint */
    LdAddrUnalign_EXCn       =   4,              /*!<  Load address misaligned */
    LdFault_EXCn             =   5,              /*!<  Load access fault */
    StAddrUnalign_EXCn       =   6,              /*!<  Store or AMO address misaligned */
    StAccessFault_EXCn       =   7,              /*!<  Store or AMO access fault */
    UmodeEcall_EXCn          =   8,              /*!<  Environment call from User mode */
    MmodeEcall_EXCn          =  11,              /*!<  Environment call from Machine mode */
    NMI_EXCn                 = 0xfff,            /*!<  NMI interrupt */
} EXCn_Type;

/* includes */
#include <nmsis_core.h>                         /*!< Nuclei N/NX class processor and core peripherals */
#include "system_gd32vw55x.h"
#include <stdint.h>

// GD32VW55x_User_Manual_Rev1.0.pdf: The RISC-V system timer (SysTick) external clock is clocked with the AHB clock (HCLK) divided by 8.
// Nuclei_N300_Series_Databook.pdf: The mtime_toggle_a is a periodic pulse signal (normally as System Tick) from the SoC system, and used to drive
// the counter of the internal TIMER unit inside the Core. After the synchronization, both the rising edge and falling edge of the signal are sampled by the
// core_clk_aon of the Core, and any detected edge will trigger the TIMER counter to increment.
// NOTE: since both systick clock rising and falling edge signal are sampled, so the timer freq is (SysCLK / 8) * 2 = SysCLK >> 2
#define SOC_TIMER_FREQ     ((uint32_t)SystemCoreClock >> 2)

/* enum definitions */
typedef enum {DISABLE = 0, ENABLE = !DISABLE} EventStatus, ControlStatus;
typedef enum {RESET = 0, SET = !RESET} FlagStatus;
typedef enum {ERROR = 0, SUCCESS = !ERROR} ErrStatus;

/* bit operations */
#define REG32(addr)                  (*(volatile uint32_t *)(uint32_t)(addr))
#define REG16(addr)                  (*(volatile uint16_t *)(uint32_t)(addr))
#define REG8(addr)                   (*(volatile uint8_t *)(uint32_t)(addr))
#define BIT(x)                       ((uint32_t)((uint32_t)0x00000001U<<(x)))
#define BITS(start, end)             ((0xFFFFFFFFUL << (start)) & (0xFFFFFFFFUL >> (31U - (uint32_t)(end))))
#define GET_BITS(regval, start, end) (((regval) & BITS((start),(end))) >> (start))

/* main flash and SRAM memory map */
#define FLASH_BASE            ((uint32_t)0x08000000U)           /*!< main FLASH base address */
#define SRAM_BASE             ((uint32_t)0x20000000U)           /*!< SRAM base address */
#define SRAM0_BASE            ((uint32_t)0x20000000U)           /*!< SRAM0 base address */
#define SRAM1_BASE            ((uint32_t)0x20010000U)           /*!< SRAM1 base address */
#define SRAM2_BASE            ((uint32_t)0x20020000U)           /*!< SRAM2 base address */
#define SRAM3_BASE            ((uint32_t)0x20030000U)           /*!< SRAM3 base address */

/* peripheral memory map */
#define APB1_BUS_BASE         ((uint32_t)0x40000000U)           /*!< apb1 base address */
#define APB2_BUS_BASE         ((uint32_t)0x40010000U)           /*!< apb2 base address */
#define AHB1_BUS_BASE         ((uint32_t)0x40020000U)           /*!< ahb1 base address */
#define AHB2_BUS_BASE         ((uint32_t)0x4C000000U)           /*!< ahb2 base address */

/* QSPI_FLASH memory map */
#define QSPI_FLASH            ((uint32_t)0x90000000U)           /*!< QSPI_FLASH base address */
/* advanced peripheral bus 1 memory map */
#define TIMER_BASE            (APB1_BUS_BASE + 0x00000000U)     /*!< TIMER base address */
#define RTC_BASE              (APB1_BUS_BASE + 0x00002800U)     /*!< RTC base address */
#define WWDGT_BASE            (APB1_BUS_BASE + 0x00002C00U)     /*!< WWDGT base address */
#define FWDGT_BASE            (APB1_BUS_BASE + 0x00003000U)     /*!< FWDGT base address */
#define USART_BASE            (APB1_BUS_BASE + 0x00004400U)     /*!< USART base address */
#define I2C_BASE              (APB1_BUS_BASE + 0x00005400U)     /*!< I2C base address */
#define PMU_BASE              (APB1_BUS_BASE + 0x00007000U)     /*!< PMU base address */

/* advanced peripheral bus 2 memory map */
#define ADC_BASE              (APB2_BUS_BASE + 0x00002000U)     /*!< ADC base address */
#define SPI_BASE              (APB2_BUS_BASE + 0x00003000U)     /*!< SPI base address */
#define EXTI_BASE             (APB2_BUS_BASE + 0x00003C00U)     /*!< EXTI base address */
#define SYSCFG_BASE           (APB2_BUS_BASE + 0x00003800U)     /*!< SYSCFG base address */
#define WIFI_RF_BASE          (APB2_BUS_BASE + 0x00007800U)     /*!< WIFI base address */

/* advanced high performance bus 1 memory map */
#define GPIO_BASE             (AHB1_BUS_BASE + 0x00000000U)     /*!< GPIO base address */
#define FMC_BASE              (AHB1_BUS_BASE + 0x00002000U)     /*!< FMC base address */
#define EFUSE_BASE            (AHB1_BUS_BASE + 0x00002800U)     /*!< EFUSE base address */
#define CRC_BASE              (AHB1_BUS_BASE + 0x00003000U)     /*!< CRC base address */
#define RCU_BASE              (AHB1_BUS_BASE + 0x00003800U)     /*!< RCU base address */
#define QSPI_REG_BASE         (AHB1_BUS_BASE + 0x00005800U)     /*!< QSPI base address */
#define DMA_BASE              (AHB1_BUS_BASE + 0x00006000U)     /*!< DMA base address */
#define WIFI_BASE             (AHB1_BUS_BASE + 0x00010000U)     /*!< WIFI11N base address */

/* advanced high performance bus 2 memory map */
#define CAU_BASE              (AHB2_BUS_BASE + 0x00060000U)     /*!< CAU base address */
#define HAU_BASE              (AHB2_BUS_BASE + 0x00060400U)     /*!< HAU base address */
#define TRNG_BASE             (AHB2_BUS_BASE + 0x00060800U)     /*!< TRNG base address */
#define PKCAU_BASE            (AHB2_BUS_BASE + 0x00061000U)     /*!< PKCAU base address */

/* debug memory map */
#define DBG_BASE              ((uint32_t)0xE0044000U)           /*!< DBG base address */

/* define marco USE_STDPERIPH_DRIVER */
#if !defined  USE_STDPERIPH_DRIVER
#define USE_STDPERIPH_DRIVER
#endif /* no define USE_STDPERIPH_DRIVER*/
#ifdef USE_STDPERIPH_DRIVER
#include "gd32vw55x_libopt.h"
#endif /* USE_STDPERIPH_DRIVER */

extern void delay_1ms(uint32_t count);
extern uint32_t get_cpu_freq(void);

#ifdef __cplusplus
}
#endif
#endif /* GD32VW55x_H */
