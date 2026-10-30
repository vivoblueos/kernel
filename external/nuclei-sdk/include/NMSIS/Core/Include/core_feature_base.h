/*
 * Copyright (c) 2019 Nuclei Limited. All rights reserved.
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

#ifndef __CORE_FEATURE_BASE__
#define __CORE_FEATURE_BASE__
/*!
 * @file     core_feature_base.h
 * @brief    Base core feature API for Nuclei N/NX Core
 */
/*
 * Core Base Feature Configuration Macro:
 * 1. __HARTID_OFFSET:  Optional, define this macro when your cpu system first hart hartid and hart index is different.
 *    eg. If your cpu system, first hart hartid is 2, hart index is 0, then set this macro to 2
 *
 */
#include <stdint.h>

#ifdef __cplusplus
 extern "C" {
#endif

#include "nmsis_compiler.h"

/**
 * \defgroup NMSIS_Core_Registers     Register Define and Type Definitions
 * \brief   Type definitions and defines for core registers.
 *
 * @{
 */
#ifndef __RISCV_XLEN
  /** \brief Refer to the width of an integer register in bits(either 32 or 64) */
  #ifndef __riscv_xlen
    #define __RISCV_XLEN    32
  #else
    #define __RISCV_XLEN    __riscv_xlen
  #endif
#endif /* __RISCV_XLEN */

/** \brief Type of Control and Status Register(CSR), depends on the XLEN defined in RISC-V */
typedef unsigned long rv_csr_t;

/** @} */ /* End of Doxygen Group NMSIS_Core_Registers */
/**
 * \defgroup NMSIS_Core_Base_Registers     Base Register Define and Type Definitions
 * \ingroup NMSIS_Core_Registers
 * \brief   Type definitions and defines for base core registers.
 *
 * @{
 */
/**
 * \brief  Union type to access MISA CSR register.
 */
typedef union {
    struct {
        rv_csr_t a:1;                           /*!< bit: 0  Atomic extension */
        rv_csr_t b:1;                           /*!< bit: 1  B extension */
        rv_csr_t c:1;                           /*!< bit: 2  Compressed extension */
        rv_csr_t d:1;                           /*!< bit: 3  Double-precision floating-point extension */
        rv_csr_t e:1;                           /*!< bit: 4  RV32E/64E base ISA */
        rv_csr_t f:1;                           /*!< bit: 5  Single-precision floating-point extension */
        rv_csr_t g:1;                           /*!< bit: 6  Reserved */
        rv_csr_t h:1;                           /*!< bit: 7  Hypervisor extension */
        rv_csr_t i:1;                           /*!< bit: 8  RV32I/64I/128I base ISA */
        rv_csr_t j:1;                           /*!< bit: 9  Reserved */
        rv_csr_t k:1;                           /*!< bit: 10 Reserved */
        rv_csr_t l:1;                           /*!< bit: 11 Reserved */
        rv_csr_t m:1;                           /*!< bit: 12 Integer Multiply/Divide extension */
        rv_csr_t n:1;                           /*!< bit: 13 Tentatively reserved for User-Level Interrupts extension */
        rv_csr_t o:1;                           /*!< bit: 14 Reserved */
        rv_csr_t p:1;                           /*!< bit: 15 Tentatively reserved for Packed-SIMD extension  */
        rv_csr_t q:1;                           /*!< bit: 16 Quad-precision floating-point extension  */
        rv_csr_t r:1;                           /*!< bit: 17 Reserved */
        rv_csr_t s:1;                           /*!< bit: 18 Supervisor mode implemented  */
        rv_csr_t t:1;                           /*!< bit: 19 Reserved */
        rv_csr_t u:1;                           /*!< bit: 20 User mode implemented  */
        rv_csr_t v:1;                           /*!< bit: 21 Vector extension  */
        rv_csr_t w:1;                           /*!< bit: 22 Reserved */
        rv_csr_t x:1;                           /*!< bit: 23 Non-standard extensions present  */
        rv_csr_t y:1;                           /*!< bit: 24 Reserved */
        rv_csr_t z:1;                           /*!< bit: 25 Reserved */
        rv_csr_t _reserved0:__RISCV_XLEN-28;    /*!< bit: 26..XLEN-3 Reserved  */
        rv_csr_t mxl:2;                         /*!< bit: XLEN-2..XLEN-1 Machine XLEN  */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MISA_Type;

/**
 * \brief  Union type to access MSTATUS CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:1;                  /*!< bit: 0  Reserved */
        rv_csr_t sie:1;                         /*!< bit: 1  supervisor interrupt enable flag */
        rv_csr_t _reserved1:1;                  /*!< bit: 2  Reserved */
        rv_csr_t mie:1;                         /*!< bit: 3  machine mode interrupt enable flag */
        rv_csr_t _reserved2:1;                  /*!< bit: 4  Reserved */
        rv_csr_t spie:1;                        /*!< bit: 5  supervisor mode interrupt enable flag */
        rv_csr_t ube:1;                         /*!< bit: 6  U-mode non-instruction-fetch memory accesse big-endian enable flag */
        rv_csr_t mpie:1;                        /*!< bit: 7  machine mode previous interrupt enable flag */
        rv_csr_t spp:1;                         /*!< bit: 8  supervisor previous privilede mode */
        rv_csr_t vs:2;                          /*!< bit: 9..10  vector status flag */
        rv_csr_t mpp:2;                         /*!< bit: 11..12 machine previous privilede mode  */
        rv_csr_t fs:2;                          /*!< bit: 13..14 FS status flag */
        rv_csr_t xs:2;                          /*!< bit: 15..16 XS status flag */
        rv_csr_t mprv:1;                        /*!< bit: 17 Modify PRiVilege */
        rv_csr_t sum:1;                         /*!< bit: 18 Supervisor Mode load and store protection */
        rv_csr_t mxr:1;                         /*!< bit: 19 Make eXecutable Readable */
        rv_csr_t tvm:1;                         /*!< bit: 20 Trap Virtual Memory */
        rv_csr_t tw:1;                          /*!< bit: 21 Timeout Wait */
        rv_csr_t tsr:1;                         /*!< bit: 22 Trap SRET */
        rv_csr_t spelp:1;                       /*!< bit: 23 Supervisor mode Previous Expected Landing Pad (ELP) State */
        rv_csr_t sdt:1;                         /*!< bit: 24 S-mode-disable-trap */
#if defined(__RISCV_XLEN) && __RISCV_XLEN == 64
        rv_csr_t _reserved3:7;                  /*!< bit: 25..31 Reserved  */
        rv_csr_t uxl:2;                         /*!< bit: 32..33 U-mode XLEN  */
        rv_csr_t sxl:2;                         /*!< bit: 34..35 S-mode XLEN  */
        rv_csr_t sbe:1;                         /*!< bit: 36 S-mode non-instruction-fetch memory accesse big-endian enable flag */
        rv_csr_t mbe:1;                         /*!< bit: 37 M-mode non-instruction-fetch memory accesse big-endian enable flag */
        rv_csr_t gva:1;                         /*!< bit: 38 Guest Virtual Address */
        rv_csr_t mpv:1;                         /*!< bit: 39 Machine Previous Virtualization Mode */
        rv_csr_t _reserved4:1;                  /*!< bit: 40 Reserved  */
        rv_csr_t mpelp:1;                       /*!< bit: 41 Machine mode Previous Expected Landing Pad (ELP) State */
        rv_csr_t mdt:1;                         /*!< bit: 42 M-mode-disable-trap */
        rv_csr_t _reserved5:20;                 /*!< bit: 43..62 Reserved  */
        rv_csr_t sd:1;                          /*!< bit: 63 Dirty status for XS or FS */
#else
        rv_csr_t _reserved3:6;                  /*!< bit: 25..30 Reserved  */
        rv_csr_t sd:1;                          /*!< bit: 31 Dirty status for XS or FS */
#endif
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MSTATUS_Type;

#if defined(__RISCV_XLEN) && __RISCV_XLEN == 32
/**
 * \brief  Union type to access MSTATUSH CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:4;                  /*!< bit: 0..3  Reserved */
        rv_csr_t sbe:1;                         /*!< bit: 4 S-mode non-instruction-fetch memory accesse big-endian enable flag */
        rv_csr_t mbe:1;                         /*!< bit: 5 M-mode non-instruction-fetch memory accesse big-endian enable flag */
        rv_csr_t gva:1;                         /*!< bit: 6 Guest Virtual Address */
        rv_csr_t mpv:1;                         /*!< bit: 7 Machine Previous Virtualization Mode */
        rv_csr_t _reserved1:1;                  /*!< bit: 8 Reserved  */
        rv_csr_t mpelp:1;                       /*!< bit: 9 Machine mode Previous Expected Landing Pad (ELP) State */
        rv_csr_t mdt:1;                         /*!< bit: 10 M-mode-disable-trap */
        rv_csr_t _reserved5:21;                 /*!< bit: 11..31 Reserved  */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MSTATUSH_Type;
#endif

/**
 * \brief  Union type to access MTVEC CSR register.
 */
typedef union {
    struct {
        rv_csr_t mode:6;                        /*!< bit: 0..5   interrupt mode control */
        rv_csr_t addr:__RISCV_XLEN-6;           /*!< bit: 6..XLEN-1  mtvec address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MTVEC_Type;

/**
 * \brief  Union type to access MCAUSE CSR register.
 */
typedef union {
    struct {
        rv_csr_t exccode:12;                    /*!< bit: 0..11  exception or interrupt code */
        rv_csr_t _reserved0:4;                  /*!< bit: 12..15  Reserved */
        rv_csr_t mpil:8;                        /*!< bit: 16..23  Previous interrupt level */
        rv_csr_t _reserved1:3;                  /*!< bit: 24..26  Reserved */
        rv_csr_t mpie:1;                        /*!< bit: 27  Interrupt enable flag before enter interrupt */
        rv_csr_t mpp:2;                         /*!< bit: 28..29  Privilede mode flag before enter interrupt */
        rv_csr_t minhv:1;                       /*!< bit: 30  Machine interrupt vector table */
#if defined(__RISCV_XLEN) && __RISCV_XLEN == 64
        rv_csr_t _reserved2:__RISCV_XLEN-32;    /*!< bit: 31..XLEN-2  Reserved */
#endif
        rv_csr_t interrupt:1;                   /*!< bit: XLEN-1  trap type. 0 means exception and 1 means interrupt */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MCAUSE_Type;

/**
 * \brief  Union type to access MCOUNTINHIBIT CSR register.
 */
typedef union {
    struct {
        rv_csr_t cy:1;                          /*!< bit: 0     1 means disable mcycle counter */
        rv_csr_t _reserved0:1;                  /*!< bit: 1     Reserved */
        rv_csr_t ir:1;                          /*!< bit: 2     1 means disable minstret counter */
        rv_csr_t _reserved1:__RISCV_XLEN-3;     /*!< bit: 3..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MCOUNTINHIBIT_Type;

/**
 * \brief  Union type to access MSUBM CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:6;                  /*!< bit: 0..5   Reserved */
        rv_csr_t typ:2;                         /*!< bit: 6..7   current trap type */
        rv_csr_t ptyp:2;                        /*!< bit: 8..9   previous trap type */
        rv_csr_t _reserved1:__RISCV_XLEN-10;    /*!< bit: 10..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MSUBM_Type;

/**
 * \brief  Union type to access MDCAUSE CSR register.
 */
typedef union {
    struct {
        rv_csr_t mdcause:3;                     /*!< bit: 0..2   More detailed exception information as MCAUSE supplement */
        rv_csr_t _reserved0:__RISCV_XLEN-3;     /*!< bit: 3..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MDCAUSE_Type;

/**
 * \brief  Union type to access MMISC_CTRL CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:1;                  /*!< bit: 0     Reserved */
        rv_csr_t zclsd_en:1;                    /*!< bit: 1     Control the Zclsd will uses the Zcf extension encoding or not */
        rv_csr_t _reserved1:1;                  /*!< bit: 2     Reserved */
        rv_csr_t bpu:1;                         /*!< bit: 3     dynamic prediction enable flag */
        rv_csr_t _reserved2:2;                  /*!< bit: 4..5  Reserved */
        rv_csr_t misalign:1;                    /*!< bit: 6     misaligned access support flag */
        rv_csr_t zcmt_zcmp:1;                   /*!< bit: 7     Zc Ext uses the cfdsp of D Ext’s encoding or not */
        rv_csr_t core_buserr:1;                 /*!< bit: 8     core bus error exception or interrupt */
        rv_csr_t nmi_cause:1;                   /*!< bit: 9     mnvec control and nmi mcase exccode */
        rv_csr_t imreturn_en:1;                 /*!< bit: 10    IMRETURN mode of trace */
        rv_csr_t sijump_en:1;                   /*!< bit: 11    SIJUMP mode of trace */
        rv_csr_t ldspec_en:1;                   /*!< bit: 12    enable load speculative goes to mem interface */
        rv_csr_t _reserved3:1;                  /*!< bit: 13    Reserved */
        rv_csr_t dbg_sec:1;                     /*!< bit: 14    debug access mode, removed in latest releases */
        rv_csr_t _reserved4:2;                  /*!< bit: 15..16 Reserved */
        rv_csr_t csr_excl_enable:1;             /*!< bit: 17    Exclusive instruction(lr,sc) on Non-cacheable/Device memory can send exclusive flag in memory bus */
        rv_csr_t _reserved5:__RISCV_XLEN-18;    /*!< bit: 18..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MMISCCTRL_Type;

typedef CSR_MMISCCTRL_Type CSR_MMISCCTL_Type;
typedef CSR_MMISCCTRL_Type CSR_MMISC_CTL_Type;

/**
 * \brief  Union type to access MCACHE_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t ic_en:1;                       /*!< bit: 0 I-Cache enable */
        rv_csr_t ic_scpd_mod:1;                 /*!< bit: 1 Scratchpad mode, 0: Scratchpad as ICache Data RAM, 1: Scratchpad as ILM SRAM */
        rv_csr_t ic_ecc_en:1;                   /*!< bit: 2 I-Cache ECC enable */
        rv_csr_t ic_ecc_excp_en:1;              /*!< bit: 3 I-Cache 2bit ECC error exception enable */
        rv_csr_t ic_rwtecc:1;                   /*!< bit: 4 Control I-Cache Tag Ram ECC code injection */
        rv_csr_t ic_rwdecc:1;                   /*!< bit: 5 Control I-Cache Data Ram ECC code injection */
        rv_csr_t ic_pf_en:1;                    /*!< bit: 6 I-Cache prefetch enable */
        rv_csr_t ic_cancel_en:1;                /*!< bit: 7 I-Cache change flow canceling enable control */
        rv_csr_t ic_ecc_chk_en:1;               /*!< bit: 8 I-Cache check ECC codes enable */
        rv_csr_t ic_prefetch_en:1;              /*!< bit: 9 I-Cache CMO prefetch enable control */
        rv_csr_t ic_burst_type:1;               /*!< bit: 10 I-Cache Burst type control */
        rv_csr_t _reserved0:5;                  /*!< bit: 11..15 Reserved */
        rv_csr_t dc_en:1;                       /*!< bit: 16 DCache enable */
        rv_csr_t dc_ecc_en:1;                   /*!< bit: 17 D-Cache ECC enable */
        rv_csr_t dc_ecc_excp_en:1;              /*!< bit: 18 D-Cache 2bit ECC error exception enable */
        rv_csr_t dc_rwtecc:1;                   /*!< bit: 19 Control D-Cache Tag Ram ECC code injection */
        rv_csr_t dc_rwdecc:1;                   /*!< bit: 20 Control D-Cache Data Ram ECC code injection */
        rv_csr_t dc_ecc_chk_en:1;               /*!< bit: 21 D-Cache check ECC codes enable */
        rv_csr_t dc_prefetch_en:1;              /*!< bit: 22 D-Cache CMO prefetch enable control */
        rv_csr_t dc_burst_type:1;               /*!< bit: 23 D-Cache Burst type control */
        rv_csr_t _reserved1:__RISCV_XLEN-24;    /*!< bit: 24..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MCACHECTL_Type;

typedef CSR_MCACHECTL_Type CSR_MCACHE_CTL_Type;

/**
 * \brief  Union type to access MSAVESTATUS CSR register.
 */
typedef union {
    struct {
        rv_csr_t mpie1:1;                       /*!< bit: 0     interrupt enable flag of fisrt level NMI/exception nestting */
        rv_csr_t mpp1:2;                        /*!< bit: 1..2  privilede mode of fisrt level NMI/exception nestting */
        rv_csr_t _reserved0:3;                  /*!< bit: 3..5  Reserved */
        rv_csr_t ptyp1:2;                       /*!< bit: 6..7  NMI/exception type of before first nestting */
        rv_csr_t mpie2:1;                       /*!< bit: 8     interrupt enable flag of second level NMI/exception nestting */
        rv_csr_t mpp2:2;                        /*!< bit: 9..10 privilede mode of second level NMI/exception nestting */
        rv_csr_t _reserved1:3;                  /*!< bit: 11..13     Reserved */
        rv_csr_t ptyp2:2;                       /*!< bit: 14..15     NMI/exception type of before second nestting */
        rv_csr_t _reserved2:__RISCV_XLEN-16;    /*!< bit: 16..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t w;                                 /*!< Type      used for csr data access */
} CSR_MSAVESTATUS_Type;

/**
 * \brief  Union type to access MILM_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t ilm_en:1;                      /*!< bit: 0 ILM enable */
        rv_csr_t ilm_ecc_en:1;                  /*!< bit: 1 ILM ECC eanble */
        rv_csr_t ilm_ecc_excp_en:1;             /*!< bit: 2 ILM ECC exception enable */
        rv_csr_t ilm_rwecc:1;                   /*!< bit: 3 Control mecc_code write to ilm, simulate error injection */
        rv_csr_t ilm_ecc_chk_en:1;              /*!< bit: 4 ILM check ECC codes enable */
        rv_csr_t ilm_va_en:1;                   /*!< bit: 5 Using virtual address to judge ILM access */
        rv_csr_t _reserved0:4;                  /*!< bit: 6..9 Reserved */
        rv_csr_t ilm_bpa:__RISCV_XLEN-10;       /*!< bit: 10..XLEN-1 ILM base address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MILMCTL_Type;

typedef CSR_MILMCTL_Type CSR_MILM_CTL_Type;

/**
 * \brief  Union type to access MDLM_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t dlm_en:1;                      /*!< bit: 0 DLM enable */
        rv_csr_t dlm_ecc_en:1;                  /*!< bit: 1 DLM ECC eanble */
        rv_csr_t dlm_ecc_excp_en:1;             /*!< bit: 2 DLM ECC exception enable */
        rv_csr_t dlm_rwecc:1;                   /*!< bit: 3 Control mecc_code write to dlm, simulate error injection */
        rv_csr_t dlm_ecc_chk_en:1;              /*!< bit: 4 DLM check ECC codes enable */
        rv_csr_t _reserved0:5;                  /*!< bit: 5..9 Reserved */
        rv_csr_t dlm_bpa:__RISCV_XLEN-10;       /*!< bit: 10..XLEN-1 DLM base address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MDLMCTL_Type;

typedef CSR_MDLMCTL_Type CSR_DILM_CTL_Type;

/**
 * \brief  Union type to access MCFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t tee:1;                         /*!< bit: 0 TEE present */
        rv_csr_t ecc:1;                         /*!< bit: 1 ECC present */
        rv_csr_t clic:1;                        /*!< bit: 2 CLIC present */
        rv_csr_t plic:1;                        /*!< bit: 3 PLIC present */
        rv_csr_t fio:1;                         /*!< bit: 4 FIO present */
        rv_csr_t ppi:1;                         /*!< bit: 5 PPI present */
        rv_csr_t nice:1;                        /*!< bit: 6 NICE present */
        rv_csr_t ilm:1;                         /*!< bit: 7 ILM present */
        rv_csr_t dlm:1;                         /*!< bit: 8 DLM present */
        rv_csr_t icache:1;                      /*!< bit: 9 ICache present */
        rv_csr_t dcache:1;                      /*!< bit: 10 DCache present */
        rv_csr_t smp:1;                         /*!< bit: 11 SMP present */
        rv_csr_t dsp_n1:1;                      /*!< bit: 12 DSP N1 present */
        rv_csr_t dsp_n2:1;                      /*!< bit: 13 DSP N2 present */
        rv_csr_t dsp_n3:1;                      /*!< bit: 14 DSP N3 present */
        rv_csr_t zc_xlcz:1;                     /*!< bit: 15 Zc and xlcz extension present */
        rv_csr_t iregion:1;                     /*!< bit: 16 IREGION present */
        rv_csr_t vpu_degree:2;                  /*!< bit: 17..18 Indicate the VPU degree of parallel */
        rv_csr_t sec_mode:1;                    /*!< bit: 19 Smwg extension present */
        rv_csr_t etrace:1;                      /*!< bit: 20 Etrace present */
        rv_csr_t safety_mecha:2;                /*!< bit: 21..22 Indicate Core's safety mechanism */
        rv_csr_t vnice:1;                       /*!< bit: 23 VNICE present */
        rv_csr_t xlcz:1;                        /*!< bit: 24 XLCZ extension present */
        rv_csr_t zilsd:1;                       /*!< bit: 25 Zilsd/Zclsd extension present */
        rv_csr_t sstc:1;                        /*!< bit: 26 SSTC extension present */
        rv_csr_t _reserved1:__RISCV_XLEN-27;    /*!< bit: 27..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MCFGINFO_Type;

typedef CSR_MCFGINFO_Type CSR_MCFG_INFO_Type;

/**
 * \brief  Union type to access MICFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t set:4;                         /*!< bit: 0..3 I-Cache sets per way */
        rv_csr_t way:3;                         /*!< bit: 4..6 I-Cache way */
        rv_csr_t lsize:3;                       /*!< bit: 7..9 I-Cache line size */
        rv_csr_t ecc:1;                         /*!< bit: 10   I-Cache ECC support */
        rv_csr_t _reserved0:5;                  /*!< bit: 11..15 Reserved */
        rv_csr_t lm_size:5;                     /*!< bit: 16..20 ILM size, need to be 2^n size */
        rv_csr_t lm_xonly:1;                    /*!< bit: 21 ILM Execute only permission or Reserved */
        rv_csr_t lm_ecc:1;                      /*!< bit: 22 ILM ECC support */
        rv_csr_t _reserved1:__RISCV_XLEN-23;    /*!< bit: 23..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MICFGINFO_Type;

typedef CSR_MICFGINFO_Type CSR_MICFG_INFO_Type;

/**
 * \brief  Union type to access MDCFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t set:4;                         /*!< bit: 0..3 D-Cache sets per way */
        rv_csr_t way:3;                         /*!< bit: 4..6 D-Cache way */
        rv_csr_t lsize:3;                       /*!< bit: 7..9 D-Cache line size */
        rv_csr_t ecc:1;                         /*!< bit: 10   D-Cache ECC support */
        rv_csr_t _reserved0:5;                  /*!< bit: 11..15 Reserved */
        rv_csr_t lm_size:5;                     /*!< bit: 16..20 DLM size, need to be 2^n size */
        rv_csr_t lm_ecc:1;                      /*!< bit: 21 DLM ECC present */
        rv_csr_t _reserved1:__RISCV_XLEN-22;    /*!< bit: 22..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MDCFGINFO_Type;

typedef CSR_MDCFGINFO_Type CSR_MDCFG_INFO_Type;

/**
 * \brief  Union type to access MTLBCFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t set:4;                         /*!< bit: 0..3  Main TLB entry per way */
        rv_csr_t way:3;                         /*!< bit: 4..6  Main TLB ways */
        rv_csr_t lsize:3;                       /*!< bit: 7..9  Main TLB line size or Reserved */
        rv_csr_t ecc:1;                         /*!< bit: 10  Main TLB supports ECC or not */
        rv_csr_t napot:1;                       /*!< bit: 11  TLB supports Svnapot or not */
        rv_csr_t _reserved1:4;                  /*!< bit: 12..15  Reserved 0 */
        rv_csr_t i_size:3;                      /*!< bit: 16..18  ITLB size */
        rv_csr_t d_size:3;                      /*!< bit: 19..21  DTLB size */
        rv_csr_t _reserved2:__RISCV_XLEN-22;    /*!< bit: 22..XLEN-1  Reserved 0 */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MTLBCFGINFO_Type;

typedef CSR_MTLBCFGINFO_Type CSR_MTLBCFG_INFO_Type;

/**
 * \brief  Union type to access MPPICFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:1;                  /*!< bit: 0 Reserved 1 */
        rv_csr_t ppi_size:5;                    /*!< bit: 1..5 PPI size, need to be 2^n size */
        rv_csr_t _reserved1:3;                  /*!< bit: 6..8 Reserved 0 */
        rv_csr_t ppi_en:1;                      /*!< bit: 9 PPI Enable. Software can write this bit to control PPI */
        rv_csr_t ppi_bpa:__RISCV_XLEN-10;       /*!< bit: 10..XLEN-1 PPI base address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MPPICFGINFO_Type;

typedef CSR_MPPICFGINFO_Type CSR_MPPICFG_INFO_Type;

/**
 * \brief  Union type to access MFIOCFG_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:1;                  /*!< bit: 0 Reserved */
        rv_csr_t fio_size:5;                    /*!< bit: 1..5 FIO size, need to be 2^n size */
        rv_csr_t _reserved1:4;                  /*!< bit: 6..9 Reserved */
        rv_csr_t fio_bpa:__RISCV_XLEN-10;       /*!< bit: 10..XLEN-1 FIO base address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MFIOCFGINFO_Type;

typedef CSR_MFIOCFGINFO_Type CSR_MFIOCFG_INFO_Type;

/**
 * \brief  Union type to access MECC_LOCK CSR register.
 */
typedef union {
    struct {
        rv_csr_t ecc_lock:1;                    /*!< bit: 0 RW permission, ECC Lock configure */
        rv_csr_t _reserved0:__RISCV_XLEN-1;     /*!< bit: 1..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MECCLOCK_Type;

typedef CSR_MECCLOCK_Type CSR_MECC_LOCK_Type;

/**
 * \brief  Union type to access MECC_CODE CSR register.
 */
typedef union {
    struct {
        rv_csr_t code:9;                        /*!< bit: 0..8 Used to inject ECC check code */
        rv_csr_t _reserved0:7;                  /*!< bit: 9..15 Reserved 0 */
        rv_csr_t ramid:5;                       /*!< bit: 16..20 The ID of RAM that has 2bit ECC error, software can clear these bits */
        rv_csr_t _reserved1:3;                  /*!< bit: 21..23 Reserved 0 */
        rv_csr_t sramid:5;                      /*!< bit: 24..28 The ID of RAM that has 1bit ECC error, software can clear these bits */
        rv_csr_t _reserved2:__RISCV_XLEN-29;    /*!< bit: 29..XLEN-1 Reserved 0 */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MECCCODE_Type;

typedef CSR_MECCCODE_Type CSR_MECC_CODE_Type;

/**
 * \brief  Union type to access MECC_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t ilm_fch_msk:1;                 /*!< bit: 0 Write 1 to disable aggregate ILM fetch ECC fatal error to safety_error output */
        rv_csr_t ilm_acc_msk:1;                 /*!< bit: 1 Write 1 to disable aggregate ILM load/store access ECC fatal error to safety_error output */
        rv_csr_t dlm_acc_msk:1;                 /*!< bit: 2 Write 1 to disable aggregate DLM access ECC fatal error to safety_error output */
        rv_csr_t ic_fch_msk:1;                  /*!< bit: 3 Write 1 to disable aggregate ICache fetch ECC fatal error to safety_error output */
        rv_csr_t dc_acc_msk:1;                  /*!< bit: 4 Write 1 to disable aggregate DCache access ECC fatal error to safety_error output */
        rv_csr_t ilm_ext_msk:1;                 /*!< bit: 5 Write 1 to disable aggregate ILM external access ECC fatal error to safety_error output */
        rv_csr_t dlm_ext_msk:1;                 /*!< bit: 6 Write 1 to disable aggregate DLM external access ECC fatal error to safety_error output */
        rv_csr_t ic_ccm_msk:1;                  /*!< bit: 7 Write 1 to disable aggregate ICache CCM ECC fatal error to safety_error output */
        rv_csr_t dc_ccm_msk:1;                  /*!< bit: 8 Write 1 to disable aggregate DCache CCM ECC fatal error to safety_error output */
        rv_csr_t dc_cpbk_msk:1;                 /*!< bit: 9 Write 1 to disable aggregate DCache CPBK ECC fatal error to safety_error output */
        rv_csr_t _reserved0:__RISCV_XLEN-10;    /*!< bit: 10..XLEN-1 Reserved 0 */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MECC_CTL_Type;

/**
 * \brief  Union type to access MECC_STATUS CSR register.
 */
typedef union {
    struct {
        rv_csr_t ilm_fch_err:1;                 /*!< bit: 0 ILM fetch ECC fatal error has occurred */
        rv_csr_t ilm_acc_err:1;                 /*!< bit: 1 ILM load/store access ECC fatal error has occurred */
        rv_csr_t dlm_acc_err:1;                 /*!< bit: 2 DLM access ECC fatal error has occurred */
        rv_csr_t ic_fch_err:1;                  /*!< bit: 3 ICache fetch ECC fatal error has occurred */
        rv_csr_t dc_acc_err:1;                  /*!< bit: 4 DCache access ECC fatal error has occurred */
        rv_csr_t ilm_ext_err:1;                 /*!< bit: 5 ILM external access ECC fatal error has occurred */
        rv_csr_t dlm_ext_err:1;                 /*!< bit: 6 DLM external access ECC fatal error has occurred */
        rv_csr_t ic_ccm_err:1;                  /*!< bit: 7 ICache CCM ECC fatal error has occurred */
        rv_csr_t dc_ccm_err:1;                  /*!< bit: 8 DCache CCM ECC fatal error has occurred */
        rv_csr_t dc_cpbk_err:1;                 /*!< bit: 9 DCache CPBK ECC fatal error has occurred */
        rv_csr_t _reserved0:__RISCV_XLEN-10;    /*!< bit: 10..XLEN-1 Reserved 0 */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MECC_STATUS_Type;

/**
 * \brief  Union type to access MIRGB_INFO CSR register.
 */
typedef union {
    struct {
        rv_csr_t _reserved0:1;                  /*!< bit: 0 Reserved */
        rv_csr_t iregion_size:5;                /*!< bit: 1..5 Indicates the size of IREGION and it should be power of 2 */
        rv_csr_t _reserved1:4;                  /*!< bit: 6..9 Reserved */
        rv_csr_t iregion_base:__RISCV_XLEN-10;  /*!< bit: 10..PA_SIZE IREGION Base Address */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MIRGB_INFO_Type;

/**
 * \brief  Union type to access MSTACK_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t ovf_track_en:1;                /*!< bit: 0 Stack overflow check or track enable */
        rv_csr_t udf_en:1;                      /*!< bit: 1 Stack underflow check enable */
        rv_csr_t mode:1;                        /*!< bit: 2 Mode of stack checking */
        rv_csr_t _reserved0:__RISCV_XLEN-3;     /*!< bit: 3..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MSTACK_CTL_Type;

/**
 * \brief  Union type to access MTLB_CTL CSR register.
 */
typedef union {
    struct {
        rv_csr_t tlb_ecc_en:1;                  /*!< bit: 0 MTLB ECC eanble */
        rv_csr_t tlb_ecc_excp_en:1;             /*!< bit: 1 MTLB double bit ECC exception enable control */
        rv_csr_t tlb_tram_ecc_inj_en:1;         /*!< bit: 2 Controls to inject the ECC Code in CSR mecc_code to MTLB tag rams */
        rv_csr_t tlb_dram_ecc_inj_en:1;         /*!< bit: 3 Controls to inject the ECC Code in CSR mecc_code to MTLB data rams */
        rv_csr_t _reserved0:2;                  /*!< bit: 4..5 Reserved */
        rv_csr_t tlb_ecc_chk_en:1;              /*!< bit: 6 Controls to check the ECC when core access to MTLB */
        rv_csr_t napot_en:1;                    /*!< bit: 7 NAPOT page enable */
        rv_csr_t _reserved1:__RISCV_XLEN-8;     /*!< bit: 8..XLEN-1 Reserved */
    } b;                                        /*!< Structure used for bit  access */
    rv_csr_t d;                                 /*!< Type      used for csr data access */
} CSR_MTLB_CTL_Type;


/** @} */ /* End of Doxygen Group NMSIS_Core_Base_Registers */

/* ###########################  Core Function Access  ########################### */
/**
 * \defgroup NMSIS_Core_CSR_Register_Access    Core CSR Register Access
 * \ingroup  NMSIS_Core
 * \brief    Functions to access the Core CSR Registers
 * \details
 *
 * The following functions or macros provide access to Core CSR registers.
 * - \ref NMSIS_Core_CSR_Encoding
 * - \ref NMSIS_Core_CSR_Registers
 *   @{
 */


#ifndef __ASSEMBLER__

#ifndef __ICCRISCV__

/**
 * \brief CSR operation Macro for csrrw instruction.
 * \details
 * Read the content of csr register to __v,
 * then write content of val into csr register, then return __v
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   value to store into the CSR register
 * \return the CSR register value before written
 */
#define __RV_CSR_SWAP(csr, val)                                 \
    ({                                                          \
        rv_csr_t __v = (unsigned long)(val);                    \
        __ASM volatile("csrrw %0, " STRINGIFY(csr) ", %1"       \
                     : "=r"(__v)                                \
                     : "rK"(__v)                                \
                     : "memory");                               \
        __v;                                                    \
    })

/**
 * \brief CSR operation Macro for csrr instruction.
 * \details
 * Read the content of csr register to __v and return it
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \return the CSR register value
 */
#define __RV_CSR_READ(csr)                                      \
    ({                                                          \
        rv_csr_t __v;                                           \
        __ASM volatile("csrr %0, " STRINGIFY(csr)               \
                     : "=r"(__v)                                \
                     :                                          \
                     : "memory");                               \
        __v;                                                    \
    })

/**
 * \brief CSR operation Macro for csrw instruction.
 * \details
 * Write the content of val to csr register
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   value to store into the CSR register
 */
#define __RV_CSR_WRITE(csr, val)                                \
    ({                                                          \
        rv_csr_t __v = (rv_csr_t)(val);                         \
        __ASM volatile("csrw " STRINGIFY(csr) ", %0"            \
                     :                                          \
                     : "rK"(__v)                                \
                     : "memory");                               \
    })

/**
 * \brief CSR operation Macro for csrrs instruction.
 * \details
 * Read the content of csr register to __v,
 * then set csr register to be __v | val, then return __v
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   Mask value to be used wih csrrs instruction
 * \return the CSR register value before written
 */
#define __RV_CSR_READ_SET(csr, val)                             \
    ({                                                          \
        rv_csr_t __v = (rv_csr_t)(val);                         \
        __ASM volatile("csrrs %0, " STRINGIFY(csr) ", %1"       \
                     : "=r"(__v)                                \
                     : "rK"(__v)                                \
                     : "memory");                               \
        __v;                                                    \
    })

/**
 * \brief CSR operation Macro for csrs instruction.
 * \details
 * Set csr register to be csr_content | val
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   Mask value to be used wih csrs instruction
 */
#define __RV_CSR_SET(csr, val)                                  \
    ({                                                          \
        rv_csr_t __v = (rv_csr_t)(val);                         \
        __ASM volatile("csrs " STRINGIFY(csr) ", %0"            \
                     :                                          \
                     : "rK"(__v)                                \
                     : "memory");                               \
    })

/**
 * \brief CSR operation Macro for csrrc instruction.
 * \details
 * Read the content of csr register to __v,
 * then set csr register to be __v & ~val, then return __v
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   Mask value to be used wih csrrc instruction
 * \return the CSR register value before written
 */
#define __RV_CSR_READ_CLEAR(csr, val)                           \
    ({                                                          \
        rv_csr_t __v = (rv_csr_t)(val);                         \
        __ASM volatile("csrrc %0, " STRINGIFY(csr) ", %1"       \
                     : "=r"(__v)                                \
                     : "rK"(__v)                                \
                     : "memory");                               \
        __v;                                                    \
    })

/**
 * \brief CSR operation Macro for csrc instruction.
 * \details
 * Set csr register to be csr_content & ~val
 * \param csr   CSR macro definition defined in
 *              \ref NMSIS_Core_CSR_Registers, eg. \ref CSR_MSTATUS
 * \param val   Mask value to be used wih csrc instruction
 */
#define __RV_CSR_CLEAR(csr, val)                                \
    ({                                                          \
        rv_csr_t __v = (rv_csr_t)(val);                         \
        __ASM volatile("csrc " STRINGIFY(csr) ", %0"            \
                     :                                          \
                     : "rK"(__v)                                \
                     : "memory");                               \
    })
#else

#include <intrinsics.h>

#define __RV_CSR_SWAP         __write_csr
#define __RV_CSR_READ         __read_csr
#define __RV_CSR_WRITE        __write_csr
#define __RV_CSR_READ_SET     __set_bits_csr
#define __RV_CSR_SET          __set_bits_csr
#define __RV_CSR_READ_CLEAR   __clear_bits_csr
#define __RV_CSR_CLEAR        __clear_bits_csr

#endif /* __ICCRISCV__ */

#endif /* __ASSEMBLER__ */

/**
 * \brief switch privilege from machine mode to others.
 * \details
 *  Execute into \ref entry_point in \ref mode(supervisor or user) with given stack
 * \param mode   privilege mode
 * \param stack   predefined stack, size should set enough
 * \param entry_point   a function pointer to execute
 */
__STATIC_INLINE void __switch_mode(uint8_t mode, uintptr_t stack, void(*entry_point)(void))
{
    unsigned long val = 0;

    /* Set MPP to the requested privilege mode */
    val = __RV_CSR_READ(CSR_MSTATUS);
    val = __RV_INSERT_FIELD(val, MSTATUS_MPP, mode);

    /* Set previous MIE disabled */
    val = __RV_INSERT_FIELD(val, MSTATUS_MPIE, 0);

    __RV_CSR_WRITE(CSR_MSTATUS, val);

    /* Set the entry point in MEPC */
    __RV_CSR_WRITE(CSR_MEPC, (unsigned long)entry_point);

    /* Set the register file */
    __ASM volatile("mv sp, %0" ::"r"(stack));

    __ASM volatile("mret");
}

/**
 * \brief   Enable IRQ Interrupts
 * \details Enables IRQ interrupts by setting the MIE-bit in the MSTATUS Register.
 * \remarks
 *          Can only be executed in Privileged modes.
 */
__STATIC_FORCEINLINE void __enable_irq(void)
{
    __RV_CSR_SET(CSR_MSTATUS, MSTATUS_MIE);
}

/**
 * \brief   Disable IRQ Interrupts
 * \details Disables IRQ interrupts by clearing the MIE-bit in the MSTATUS Register.
 * \remarks
 *          Can only be executed in Privileged modes.
 */
__STATIC_FORCEINLINE void __disable_irq(void)
{
    __RV_CSR_CLEAR(CSR_MSTATUS, MSTATUS_MIE);
}

/**
 * \brief   Enable External IRQ Interrupts
 * \details Enables External IRQ interrupts by setting the MEIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_ext_irq(void)
{
    __RV_CSR_SET(CSR_MIE, MIE_MEIE);
}

/**
 * \brief   Disable External IRQ Interrupts
 * \details Disables External IRQ interrupts by clearing the MEIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_ext_irq(void)
{
    __RV_CSR_CLEAR(CSR_MIE, MIE_MEIE);
}

/**
 * \brief   Enable Timer IRQ Interrupts
 * \details Enables Timer IRQ interrupts by setting the MTIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_timer_irq(void)
{
    __RV_CSR_SET(CSR_MIE, MIE_MTIE);
}

/**
 * \brief   Disable Timer IRQ Interrupts
 * \details Disables Timer IRQ interrupts by clearing the MTIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_timer_irq(void)
{
    __RV_CSR_CLEAR(CSR_MIE, MIE_MTIE);
}

/**
 * \brief   Enable software IRQ Interrupts
 * \details Enables software IRQ interrupts by setting the MSIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_sw_irq(void)
{
    __RV_CSR_SET(CSR_MIE, MIE_MSIE);
}

/**
 * \brief   Disable software IRQ Interrupts
 * \details Disables software IRQ interrupts by clearing the MSIE-bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_sw_irq(void)
{
    __RV_CSR_CLEAR(CSR_MIE, MIE_MSIE);
}

/**
 * \brief   Disable Core IRQ Interrupt
 * \details Disable Core IRQ interrupt by clearing the irq bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_core_irq(uint32_t irq)
{
    __RV_CSR_CLEAR(CSR_MIE, 1UL << irq);
}

/**
 * \brief   Enable Core IRQ Interrupt
 * \details Enable Core IRQ interrupt by setting the irq bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_core_irq(uint32_t irq)
{
    __RV_CSR_SET(CSR_MIE, 1UL << irq);
}

/**
 * \brief   Get Core IRQ Interrupt Pending status
 * \details Get Core IRQ interrupt pending status of irq bit.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE uint32_t __get_core_irq_pending(uint32_t irq)
{
    return ((__RV_CSR_READ(CSR_MIP) >> irq) & 0x1);
}

/**
 * \brief   Clear Core IRQ Interrupt Pending status
 * \details Clear Core IRQ interrupt pending status of irq bit.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __clear_core_irq_pending(uint32_t irq)
{
    __RV_CSR_CLEAR(CSR_MIP, 1UL << irq);
}

/**
 * \brief   Enable IRQ Interrupts in supervisor mode
 * \details Enables IRQ interrupts by setting the SIE-bit in the SSTATUS Register.
 * \remarks
 *          Can only be executed in Privileged modes.
 */
__STATIC_FORCEINLINE void __enable_irq_s(void)
{
    __RV_CSR_SET(CSR_SSTATUS, SSTATUS_SIE);
}

/**
 * \brief   Disable IRQ Interrupts in supervisor mode
 * \details Disables IRQ interrupts by clearing the SIE-bit in the SSTATUS Register.
 * \remarks
 *          Can only be executed in Privileged modes.
 */
__STATIC_FORCEINLINE void __disable_irq_s(void)
{
    __RV_CSR_CLEAR(CSR_SSTATUS, SSTATUS_SIE);
}

/**
 * \brief   Enable External IRQ Interrupts in supervisor mode
 * \details Enables External IRQ interrupts by setting the SEIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_ext_irq_s(void)
{
    __RV_CSR_SET(CSR_SIE, MIE_SEIE);
}

/**
 * \brief   Disable External IRQ Interrupts in supervisor mode
 * \details Disables External IRQ interrupts by clearing the SEIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_ext_irq_s(void)
{
    __RV_CSR_CLEAR(CSR_SIE, MIE_SEIE);
}

/**
 * \brief   Enable Timer IRQ Interrupts in supervisor mode
 * \details Enables Timer IRQ interrupts by setting the STIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_timer_irq_s(void)
{
    __RV_CSR_SET(CSR_SIE, MIE_STIE);
}

/**
 * \brief   Disable Timer IRQ Interrupts in supervisor mode
 * \details Disables Timer IRQ interrupts by clearing the STIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_timer_irq_s(void)
{
    __RV_CSR_CLEAR(CSR_SIE, MIE_STIE);
}

/**
 * \brief   Enable software IRQ Interrupts in supervisor mode
 * \details Enables software IRQ interrupts by setting the SSIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_sw_irq_s(void)
{
    __RV_CSR_SET(CSR_SIE, MIE_SSIE);
}

/**
 * \brief   Disable software IRQ Interrupts in supervisor mode
 * \details Disables software IRQ interrupts by clearing the SSIE-bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_sw_irq_s(void)
{
    __RV_CSR_CLEAR(CSR_SIE, MIE_SSIE);
}

/**
 * \brief   Disable Core IRQ Interrupt in supervisor mode
 * \details Disable Core IRQ interrupt by clearing the irq bit in the SIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __disable_core_irq_s(uint32_t irq)
{
    __RV_CSR_CLEAR(CSR_SIE, 1UL << irq);
}

/**
 * \brief   Enable Core IRQ Interrupt in supervisor mode
 * \details Enable Core IRQ interrupt by setting the irq bit in the MIE Register.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __enable_core_irq_s(uint32_t irq)
{
    __RV_CSR_SET(CSR_SIE, 1UL << irq);
}

/**
 * \brief   Get Core IRQ Interrupt Pending status in supervisor mode
 * \details Get Core IRQ interrupt pending status of irq bit.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE uint32_t __get_core_irq_pending_s(uint32_t irq)
{
    return ((__RV_CSR_READ(CSR_SIP) >> irq) & 0x1);
}

/**
 * \brief   Clear Core IRQ Interrupt Pending status in supervisor mode
 * \details Clear Core IRQ interrupt pending status of irq bit.
 * \remarks
 *          Can only be executed in Privileged modes, available for plic interrupt mode.
 */
__STATIC_FORCEINLINE void __clear_core_irq_pending_s(uint32_t irq)
{
    __RV_CSR_CLEAR(CSR_SIP, 1UL << irq);
}

/**
 * \brief   Read whole 64 bits value of mcycle counter
 * \details This function will read the whole 64 bits of MCYCLE register
 * \return  The whole 64 bits value of MCYCLE
 * \remarks It will work for both RV32 and RV64 to get full 64bits value of MCYCLE
 */
__STATIC_INLINE uint64_t __get_rv_cycle(void)
{
#if __RISCV_XLEN == 32
    volatile uint32_t high0, low, high;
    uint64_t full;

    high0 = __RV_CSR_READ(CSR_MCYCLEH);
    low = __RV_CSR_READ(CSR_MCYCLE);
    high = __RV_CSR_READ(CSR_MCYCLEH);
    if (high0 != high) {
        low = __RV_CSR_READ(CSR_MCYCLE);
    }
    full = (((uint64_t)high) << 32) | low;
    return full;
#elif __RISCV_XLEN == 64
    return (uint64_t)__RV_CSR_READ(CSR_MCYCLE);
#else // TODO Need cover for XLEN=128 case in future
    return (uint64_t)__RV_CSR_READ(CSR_MCYCLE);
#endif
}

/**
 * \brief   Set whole 64 bits value of mcycle counter
 * \details This function will set the whole 64 bits of MCYCLE register
 * \remarks It will work for both RV32 and RV64 to set full 64bits value of MCYCLE
 */
__STATIC_FORCEINLINE void __set_rv_cycle(uint64_t cycle)
{
#if __RISCV_XLEN == 32
    __RV_CSR_WRITE(CSR_MCYCLE, 0); // prevent carry
    __RV_CSR_WRITE(CSR_MCYCLEH, (uint32_t)(cycle >> 32));
    __RV_CSR_WRITE(CSR_MCYCLE, (uint32_t)(cycle));
#elif __RISCV_XLEN == 64
    __RV_CSR_WRITE(CSR_MCYCLE, cycle);
#else // TODO Need cover for XLEN=128 case in future
#endif
}

/**
 * \brief   Read whole 64 bits value of machine instruction-retired counter
 * \details This function will read the whole 64 bits of MINSTRET register
 * \return  The whole 64 bits value of MINSTRET
 * \remarks It will work for both RV32 and RV64 to get full 64bits value of MINSTRET
 */
__STATIC_INLINE uint64_t __get_rv_instret(void)
{
#if __RISCV_XLEN == 32
    volatile uint32_t high0, low, high;
    uint64_t full;

    high0 = __RV_CSR_READ(CSR_MINSTRETH);
    low = __RV_CSR_READ(CSR_MINSTRET);
    high = __RV_CSR_READ(CSR_MINSTRETH);
    if (high0 != high) {
        low = __RV_CSR_READ(CSR_MINSTRET);
    }
    full = (((uint64_t)high) << 32) | low;
    return full;
#elif __RISCV_XLEN == 64
    return (uint64_t)__RV_CSR_READ(CSR_MINSTRET);
#else // TODO Need cover for XLEN=128 case in future
    return (uint64_t)__RV_CSR_READ(CSR_MINSTRET);
#endif
}

/**
 * \brief   Set whole 64 bits value of machine instruction-retired counter
 * \details This function will set the whole 64 bits of MINSTRET register
 * \remarks It will work for both RV32 and RV64 to set full 64bits value of MINSTRET
 */
__STATIC_FORCEINLINE void __set_rv_instret(uint64_t instret)
{
#if __RISCV_XLEN == 32
    __RV_CSR_WRITE(CSR_MINSTRET, 0); // prevent carry
    __RV_CSR_WRITE(CSR_MINSTRETH, (uint32_t)(instret >> 32));
    __RV_CSR_WRITE(CSR_MINSTRET, (uint32_t)(instret));
#elif __RISCV_XLEN == 64
    __RV_CSR_WRITE(CSR_MINSTRET, instret);
#else // TODO Need cover for XLEN=128 case in future
#endif
}

/**
 * \brief   Read whole 64 bits value of real-time clock
 * \details This function will read the whole 64 bits of TIME register
 * \return  The whole 64 bits value of TIME CSR
 * \remarks It will work for both RV32 and RV64 to get full 64bits value of TIME
 * \attention only available when user mode available
 */
__STATIC_INLINE uint64_t __get_rv_time(void)
{
#if __RISCV_XLEN == 32
    volatile uint32_t high0, low, high;
    uint64_t full;

    high0 = __RV_CSR_READ(CSR_TIMEH);
    low = __RV_CSR_READ(CSR_TIME);
    high = __RV_CSR_READ(CSR_TIMEH);
    if (high0 != high) {
        low = __RV_CSR_READ(CSR_TIME);
    }
    full = (((uint64_t)high) << 32) | low;
    return full;
#elif __RISCV_XLEN == 64
    return (uint64_t)__RV_CSR_READ(CSR_TIME);
#else // TODO Need cover for XLEN=128 case in future
    return (uint64_t)__RV_CSR_READ(CSR_TIME);
#endif
}

/**
 * \brief   Read the CYCLE register
 * \details This function will read the CYCLE register without taking the
 *          CYCLEH register into account
 * \return  32 bits value when XLEN=32
 *          64 bits value when XLEN=64
 *          TODO: XLEN=128 need to be supported
 */
__STATIC_FORCEINLINE unsigned long __read_cycle_csr()
{
    return __RV_CSR_READ(CSR_CYCLE);
}

/**
 * \brief   Read the INSTRET register
 * \details This function will read the INSTRET register without taking the
 *          INSTRETH register into account
 * \return  32 bits value when XLEN=32
 *          64 bits value when XLEN=64
 *          TODO: XLEN=128 need to be supported
 */
__STATIC_FORCEINLINE unsigned long __read_instret_csr()
{
    return __RV_CSR_READ(CSR_INSTRET);
}

/**
 * \brief   Read the TIME register
 * \details This function will read the TIME register without taking the
 *          TIMEH register into account
 * \return  32 bits value when XLEN=32
 *          64 bits value when XLEN=64
 *          TODO: XLEN=128 need to be supported
 */
__STATIC_FORCEINLINE unsigned long __read_time_csr()
{
    return __RV_CSR_READ(CSR_TIME);
}

/**
 * \brief   Get cluster id of current cluster
 * \details This function will get cluster id of current cluster in a multiple cluster system
 * \return  The cluster id of current cluster
 * \remarks mhartid bit 15-8 is designed for cluster id in nuclei subsystem reference design
 * \attention function is allowed in machine mode only
 */
__STATIC_FORCEINLINE unsigned long __get_cluster_id(void)
{
    unsigned long id;

    id = (__RV_CSR_READ(CSR_MHARTID) >> 8) & 0xFF;
    return id;
}

/**
 * \brief   Get hart index of current cluster
 * \details This function will get hart index of current cluster in a multiple cluster system,
 * hart index is hartid - hartid offset, for example if your hartid is 1, and offset is 1, then
 * hart index is 0
 * \return  The hart index of current cluster
 * \attention function is allowed in machine mode only
 */
__STATIC_FORCEINLINE unsigned long __get_hart_index(void)
{
    unsigned long id;
#ifdef __HARTID_OFFSET
    id = __RV_CSR_READ(CSR_MHARTID) - __HARTID_OFFSET;
#else
    id = __RV_CSR_READ(CSR_MHARTID);
#endif
    return id;
}

/**
 * \brief   Get hart id of current cluster
 * \details This function will get hart id of current cluster in a multiple cluster system
 * \return  The hart id of current cluster
 * \remarks it will return full hartid not part of it for reference subsystem design,
 * if your reference subsystem design has hartid offset, please define __HARTID_OFFSET in
 * <Device>.h
 * \attention function is allowed in machine mode only
 */
__STATIC_FORCEINLINE unsigned long __get_hart_id(void)
{
    unsigned long id;
    id = __RV_CSR_READ(CSR_MHARTID);
    return id;
}


/**
 * \brief   Get cluster id of current cluster in supervisor mode
 * \details This function will get cluster id of current cluster in a multiple cluster system
 * \return  The cluster id of current cluster
 * \remarks hartid bit 15-8 is designed for cluster id in nuclei subsystem reference design
 * \attention function is allowed in machine/supervisor mode,
 * currently only present in 600/900 series from 2024 released version
 */
__STATIC_FORCEINLINE unsigned long __get_cluster_id_s(void)
{
    unsigned long id;

    id = (__RV_CSR_READ(CSR_SHARTID) >> 8) & 0xFF;
    return id;
}

/**
 * \brief   Get hart index of current cluster in supervisor mode
 * \details This function will get hart index of current cluster in a multiple cluster system,
 * hart index is hartid - hartid offset, for example if your hartid is 1, and offset is 1, then
 * hart index is 0
 * \return  The hart index of current cluster
 * \attention function is allowed in machine/supervisor mode,
 * currently only present in 600/900 series from 2024 released version
 */
__STATIC_FORCEINLINE unsigned long __get_hart_index_s(void)
{
    unsigned long id;
#ifdef __HARTID_OFFSET
    id = __RV_CSR_READ(CSR_SHARTID) - __HARTID_OFFSET;
#else
    id = __RV_CSR_READ(CSR_SHARTID);
#endif
    return id;
}

/**
 * \brief   Get hart id of current cluster in supervisor mode
 * \details This function will get hart id of current cluster in a multiple cluster system
 * \return  The hart id of current cluster
 * \remarks it will return full hartid not part of it for reference subsystem design,
 * if your reference subsystem design has hartid offset, please define __HARTID_OFFSET in
 * <Device>.h
 * \attention function is allowed in machine/supervisor mode,
 * currently only present in 600/900 series from 2024 released version
 */
__STATIC_FORCEINLINE unsigned long __get_hart_id_s(void)
{
    unsigned long id;
    id = __RV_CSR_READ(CSR_SHARTID);
    return id;
}

/** @} */ /* End of Doxygen Group NMSIS_Core_CSR_Register_Access */

/* ###########################  CPU Intrinsic Functions ########################### */
/**
 * \defgroup NMSIS_Core_CPU_Intrinsic   Intrinsic Functions for CPU Intructions
 * \ingroup  NMSIS_Core
 * \brief    Functions that generate RISC-V CPU instructions.
 * \details
 *
 * The following functions generate specified RISC-V instructions that cannot be directly accessed by compiler.
 *   @{
 */

/**
 * \brief   NOP Instruction
 * \details
 * No Operation does nothing.
 * This instruction can be used for code alignment purposes.
 */
__STATIC_FORCEINLINE void __NOP(void)
{
    __ASM volatile("nop");
}

/**
 * \brief   Wait For Interrupt
 * \details
 * Wait For Interrupt is is executed using CSR_WFE.WFE=0 and WFI instruction.
 * It will suspends execution until interrupt, NMI or Debug happened.
 * When Core is waked up by interrupt, if
 * 1. mstatus.MIE == 1(interrupt enabled), Core will enter ISR code
 * 2. mstatus.MIE == 0(interrupt disabled), Core will resume previous execution
 */
__STATIC_FORCEINLINE void __WFI(void)
{
    __RV_CSR_CLEAR(CSR_WFE, WFE_WFE);
    __ASM volatile("wfi");
}

/**
 * \brief   Wait For Event
 * \details
 * Wait For Event is executed using CSR_WFE.WFE=1 and WFI instruction.
 * It will suspends execution until event, NMI or Debug happened.
 * When Core is waked up, Core will resume previous execution
 */
__STATIC_FORCEINLINE void __WFE(void)
{
    __RV_CSR_SET(CSR_WFE, WFE_WFE);
    __ASM volatile("wfi");
    __RV_CSR_CLEAR(CSR_WFE, WFE_WFE);
}

/**
 * \brief   Breakpoint Instruction
 * \details
 * Causes the processor to enter Debug state.
 * Debug tools can use this to investigate system state
 * when the instruction at a particular address is reached.
 */
__STATIC_FORCEINLINE void __EBREAK(void)
{
    __ASM volatile("ebreak");
}

/**
 * \brief   Environment Call Instruction
 * \details
 * The ECALL instruction is used to make a service request to
 * the execution environment.
 */
__STATIC_FORCEINLINE void __ECALL(void)
{
    __ASM volatile("ecall");
}

/**
 * \brief WFI Sleep Mode enumeration
 */
typedef enum WFI_SleepMode {
    WFI_SHALLOW_SLEEP = 0,      /*!< Shallow sleep mode, the core_clk will poweroff */
    WFI_DEEP_SLEEP = 1          /*!< Deep sleep mode, the core_clk and core_ano_clk will poweroff */
} WFI_SleepMode_Type;

/**
 * \brief   Set Sleep mode of WFI
 * \details
 * Set the SLEEPVALUE CSR register to control the
 * WFI Sleep mode.
 * \param[in] mode      The sleep mode to be set
 */
__STATIC_FORCEINLINE void __set_wfi_sleepmode(WFI_SleepMode_Type mode)
{
    __RV_CSR_WRITE(CSR_SLEEPVALUE, mode);
}

/**
 * \brief   Send TX Event
 * \details
 * Set the CSR TXEVT to control send a TX Event.
 * The Core will output signal tx_evt as output event signal.
 */
__STATIC_FORCEINLINE void __TXEVT(void)
{
    __RV_CSR_SET(CSR_TXEVT, 0x1);
}

/**
 * \brief   Enable MCYCLE counter
 * \details
 * Clear the CY bit of MCOUNTINHIBIT to 0 to enable MCYCLE Counter
 */
__STATIC_FORCEINLINE void __enable_mcycle_counter(void)
{
    __RV_CSR_CLEAR(CSR_MCOUNTINHIBIT, MCOUNTINHIBIT_CY);
}

/**
 * \brief   Disable MCYCLE counter
 * \details
 * Set the CY bit of MCOUNTINHIBIT to 1 to disable MCYCLE Counter
 */
__STATIC_FORCEINLINE void __disable_mcycle_counter(void)
{
    __RV_CSR_SET(CSR_MCOUNTINHIBIT, MCOUNTINHIBIT_CY);
}

/**
 * \brief   Enable MINSTRET counter
 * \details
 * Clear the IR bit of MCOUNTINHIBIT to 0 to enable MINSTRET Counter
 */
__STATIC_FORCEINLINE void __enable_minstret_counter(void)
{
    __RV_CSR_CLEAR(CSR_MCOUNTINHIBIT, MCOUNTINHIBIT_IR);
}

/**
 * \brief   Disable MINSTRET counter
 * \details
 * Set the IR bit of MCOUNTINHIBIT to 1 to disable MINSTRET Counter
 */
__STATIC_FORCEINLINE void __disable_minstret_counter(void)
{
    __RV_CSR_SET(CSR_MCOUNTINHIBIT, MCOUNTINHIBIT_IR);
}

/**
 * \brief   Enable selected hardware performance monitor counter
 * \param [in]    idx   the index of the hardware performance monitor counter
 * \details
 * enable selected hardware performance monitor counter mhpmcounterx.
 */
__STATIC_FORCEINLINE void __enable_mhpm_counter(unsigned long idx)
{
    __RV_CSR_CLEAR(CSR_MCOUNTINHIBIT, (1UL << idx));
}

/**
 * \brief   Disable selected hardware performance monitor counter
 * \param [in]    idx   the index of the hardware performance monitor counter
 * \details
 * Disable selected hardware performance monitor counter mhpmcounterx.
 */
__STATIC_FORCEINLINE void __disable_mhpm_counter(unsigned long idx)
{
    __RV_CSR_SET(CSR_MCOUNTINHIBIT, (1UL << idx));
}

/**
 * \brief   Enable hardware performance counters with mask
 * \param [in]    mask   mask of selected hardware performance monitor counters
 * \details
 * enable mhpmcounterx with mask, only the masked ones will be enabled.
 * mhpmcounter3-mhpmcount31 are for high performance monitor counters.
 */
__STATIC_FORCEINLINE void __enable_mhpm_counters(unsigned long mask)
{
    __RV_CSR_CLEAR(CSR_MCOUNTINHIBIT, mask);
}

/**
 * \brief   Disable hardware performance counters with mask
 * \param [in]    mask   mask of selected hardware performance monitor counters
 * \details
 * Disable mhpmcounterx with mask, only the masked ones will be disabled.
 * mhpmcounter3-mhpmcount31 are for high performance monitor counters.
 */
__STATIC_FORCEINLINE void __disable_mhpm_counters(unsigned long mask)
{
    __RV_CSR_SET(CSR_MCOUNTINHIBIT, mask);
}

/**
 * \brief   Enable all MCYCLE & MINSTRET & MHPMCOUNTER counter
 * \details
 * Clear all to zero to enable all counters,
 * such as cycle, instret, high performance monitor counters
 */
__STATIC_FORCEINLINE void __enable_all_counter(void)
{
    __RV_CSR_CLEAR(CSR_MCOUNTINHIBIT, 0xFFFFFFFF);
}

/**
 * \brief   Disable all MCYCLE & MINSTRET & MHPMCOUNTER counter
 * \details
 * Set all to one to disable all counters,
 * such as cycle, instret, high performance monitor counters
 */
__STATIC_FORCEINLINE void __disable_all_counter(void)
{
    __RV_CSR_SET(CSR_MCOUNTINHIBIT, 0xFFFFFFFF);
}

/**
 * \brief   Set event for selected high performance monitor event
 * \param [in]    idx     HPMEVENTx CSR index(3-31)
 * \param [in]    event   HPMEVENTx Register value to set
 * \details
 * Set event for high performance monitor event register
 */
__STATIC_INLINE void __set_hpm_event(unsigned long idx, unsigned long event)
{
    switch (idx) {
        case 3: __RV_CSR_WRITE(CSR_MHPMEVENT3, event); break;
        case 4: __RV_CSR_WRITE(CSR_MHPMEVENT4, event); break;
        case 5: __RV_CSR_WRITE(CSR_MHPMEVENT5, event); break;
        case 6: __RV_CSR_WRITE(CSR_MHPMEVENT6, event); break;
        case 7: __RV_CSR_WRITE(CSR_MHPMEVENT7, event); break;
        case 8: __RV_CSR_WRITE(CSR_MHPMEVENT8, event); break;
        case 9: __RV_CSR_WRITE(CSR_MHPMEVENT9, event); break;
        case 10: __RV_CSR_WRITE(CSR_MHPMEVENT10, event); break;
        case 11: __RV_CSR_WRITE(CSR_MHPMEVENT11, event); break;
        case 12: __RV_CSR_WRITE(CSR_MHPMEVENT12, event); break;
        case 13: __RV_CSR_WRITE(CSR_MHPMEVENT13, event); break;
        case 14: __RV_CSR_WRITE(CSR_MHPMEVENT14, event); break;
        case 15: __RV_CSR_WRITE(CSR_MHPMEVENT15, event); break;
        case 16: __RV_CSR_WRITE(CSR_MHPMEVENT16, event); break;
        case 17: __RV_CSR_WRITE(CSR_MHPMEVENT17, event); break;
        case 18: __RV_CSR_WRITE(CSR_MHPMEVENT18, event); break;
        case 19: __RV_CSR_WRITE(CSR_MHPMEVENT19, event); break;
        case 20: __RV_CSR_WRITE(CSR_MHPMEVENT20, event); break;
        case 21: __RV_CSR_WRITE(CSR_MHPMEVENT21, event); break;
        case 22: __RV_CSR_WRITE(CSR_MHPMEVENT22, event); break;
        case 23: __RV_CSR_WRITE(CSR_MHPMEVENT23, event); break;
        case 24: __RV_CSR_WRITE(CSR_MHPMEVENT24, event); break;
        case 25: __RV_CSR_WRITE(CSR_MHPMEVENT25, event); break;
        case 26: __RV_CSR_WRITE(CSR_MHPMEVENT26, event); break;
        case 27: __RV_CSR_WRITE(CSR_MHPMEVENT27, event); break;
        case 28: __RV_CSR_WRITE(CSR_MHPMEVENT28, event); break;
        case 29: __RV_CSR_WRITE(CSR_MHPMEVENT29, event); break;
        case 30: __RV_CSR_WRITE(CSR_MHPMEVENT30, event); break;
        case 31: __RV_CSR_WRITE(CSR_MHPMEVENT31, event); break;
        default: break;
    }
}

/**
 * \brief   Get event for selected high performance monitor event
 * \param [in]    idx     HPMEVENTx CSR index(3-31)
 * \param [in]    event   HPMEVENTx Register value to set
 * \details
 * Get high performance monitor event register value
 * \return               HPMEVENTx Register value
 */
__STATIC_INLINE unsigned long __get_hpm_event(unsigned long idx)
{
    switch (idx) {
        case 3: return __RV_CSR_READ(CSR_MHPMEVENT3);
        case 4: return __RV_CSR_READ(CSR_MHPMEVENT4);
        case 5: return __RV_CSR_READ(CSR_MHPMEVENT5);
        case 6: return __RV_CSR_READ(CSR_MHPMEVENT6);
        case 7: return __RV_CSR_READ(CSR_MHPMEVENT7);
        case 8: return __RV_CSR_READ(CSR_MHPMEVENT8);
        case 9: return __RV_CSR_READ(CSR_MHPMEVENT9);
        case 10: return __RV_CSR_READ(CSR_MHPMEVENT10);
        case 11: return __RV_CSR_READ(CSR_MHPMEVENT11);
        case 12: return __RV_CSR_READ(CSR_MHPMEVENT12);
        case 13: return __RV_CSR_READ(CSR_MHPMEVENT13);
        case 14: return __RV_CSR_READ(CSR_MHPMEVENT14);
        case 15: return __RV_CSR_READ(CSR_MHPMEVENT15);
        case 16: return __RV_CSR_READ(CSR_MHPMEVENT16);
        case 17: return __RV_CSR_READ(CSR_MHPMEVENT17);
        case 18: return __RV_CSR_READ(CSR_MHPMEVENT18);
        case 19: return __RV_CSR_READ(CSR_MHPMEVENT19);
        case 20: return __RV_CSR_READ(CSR_MHPMEVENT20);
        case 21: return __RV_CSR_READ(CSR_MHPMEVENT21);
        case 22: return __RV_CSR_READ(CSR_MHPMEVENT22);
        case 23: return __RV_CSR_READ(CSR_MHPMEVENT23);
        case 24: return __RV_CSR_READ(CSR_MHPMEVENT24);
        case 25: return __RV_CSR_READ(CSR_MHPMEVENT25);
        case 26: return __RV_CSR_READ(CSR_MHPMEVENT26);
        case 27: return __RV_CSR_READ(CSR_MHPMEVENT27);
        case 28: return __RV_CSR_READ(CSR_MHPMEVENT28);
        case 29: return __RV_CSR_READ(CSR_MHPMEVENT29);
        case 30: return __RV_CSR_READ(CSR_MHPMEVENT30);
        case 31: return __RV_CSR_READ(CSR_MHPMEVENT31);
        default: return 0;
    }
}

/**
 * \brief   Set value for selected high performance monitor counter
 * \param [in]    idx     HPMCOUNTERx CSR index(3-31)
 * \param [in]    value   HPMCOUNTERx Register value to set
 * \details
 * Set value for high performance monitor couner register
 */
__STATIC_INLINE void __set_hpm_counter(unsigned long idx, uint64_t value)
{
    switch (idx) {
#if __RISCV_XLEN == 32
        case 3: __RV_CSR_WRITE(CSR_MHPMCOUNTER3, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER3H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER3, (uint32_t)(value)); break;
        case 4: __RV_CSR_WRITE(CSR_MHPMCOUNTER4, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER4H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER4, (uint32_t)(value)); break;
        case 5: __RV_CSR_WRITE(CSR_MHPMCOUNTER5, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER5H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER5, (uint32_t)(value)); break;
        case 6: __RV_CSR_WRITE(CSR_MHPMCOUNTER6, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER6H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER6, (uint32_t)(value)); break;
        case 7: __RV_CSR_WRITE(CSR_MHPMCOUNTER7, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER7H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER7, (uint32_t)(value)); break;
        case 8: __RV_CSR_WRITE(CSR_MHPMCOUNTER8, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER8H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER8, (uint32_t)(value)); break;
        case 9: __RV_CSR_WRITE(CSR_MHPMCOUNTER9, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER9H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER9, (uint32_t)(value)); break;
        case 10: __RV_CSR_WRITE(CSR_MHPMCOUNTER10, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER10H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER10, (uint32_t)(value)); break;
        case 11: __RV_CSR_WRITE(CSR_MHPMCOUNTER11, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER11H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER11, (uint32_t)(value)); break;
        case 12: __RV_CSR_WRITE(CSR_MHPMCOUNTER12, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER12H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER12, (uint32_t)(value)); break;
        case 13: __RV_CSR_WRITE(CSR_MHPMCOUNTER13, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER13H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER13, (uint32_t)(value)); break;
        case 14: __RV_CSR_WRITE(CSR_MHPMCOUNTER14, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER14H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER14, (uint32_t)(value)); break;
        case 15: __RV_CSR_WRITE(CSR_MHPMCOUNTER15, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER15H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER15, (uint32_t)(value)); break;
        case 16: __RV_CSR_WRITE(CSR_MHPMCOUNTER16, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER16H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER16, (uint32_t)(value)); break;
        case 17: __RV_CSR_WRITE(CSR_MHPMCOUNTER17, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER17H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER17, (uint32_t)(value)); break;
        case 18: __RV_CSR_WRITE(CSR_MHPMCOUNTER18, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER18H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER18, (uint32_t)(value)); break;
        case 19: __RV_CSR_WRITE(CSR_MHPMCOUNTER19, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER19H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER19, (uint32_t)(value)); break;
        case 20: __RV_CSR_WRITE(CSR_MHPMCOUNTER20, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER20H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER20, (uint32_t)(value)); break;
        case 21: __RV_CSR_WRITE(CSR_MHPMCOUNTER21, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER21H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER21, (uint32_t)(value)); break;
        case 22: __RV_CSR_WRITE(CSR_MHPMCOUNTER22, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER22H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER22, (uint32_t)(value)); break;
        case 23: __RV_CSR_WRITE(CSR_MHPMCOUNTER23, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER23H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER23, (uint32_t)(value)); break;
        case 24: __RV_CSR_WRITE(CSR_MHPMCOUNTER24, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER24H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER24, (uint32_t)(value)); break;
        case 25: __RV_CSR_WRITE(CSR_MHPMCOUNTER25, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER25H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER25, (uint32_t)(value)); break;
        case 26: __RV_CSR_WRITE(CSR_MHPMCOUNTER26, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER26H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER26, (uint32_t)(value)); break;
        case 27: __RV_CSR_WRITE(CSR_MHPMCOUNTER27, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER27H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER27, (uint32_t)(value)); break;
        case 28: __RV_CSR_WRITE(CSR_MHPMCOUNTER28, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER28H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER28, (uint32_t)(value)); break;
        case 29: __RV_CSR_WRITE(CSR_MHPMCOUNTER29, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER29H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER29, (uint32_t)(value)); break;
        case 30: __RV_CSR_WRITE(CSR_MHPMCOUNTER30, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER30H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER30, (uint32_t)(value)); break;
        case 31: __RV_CSR_WRITE(CSR_MHPMCOUNTER31, 0); // prevent carry
            __RV_CSR_WRITE(CSR_MHPMCOUNTER31H, (uint32_t)(value >> 32));
            __RV_CSR_WRITE(CSR_MHPMCOUNTER31, (uint32_t)(value)); break;

#elif __RISCV_XLEN == 64
        case 3: __RV_CSR_WRITE(CSR_MHPMCOUNTER3, (value)); break;
        case 4: __RV_CSR_WRITE(CSR_MHPMCOUNTER4, (value)); break;
        case 5: __RV_CSR_WRITE(CSR_MHPMCOUNTER5, (value)); break;
        case 6: __RV_CSR_WRITE(CSR_MHPMCOUNTER6, (value)); break;
        case 7: __RV_CSR_WRITE(CSR_MHPMCOUNTER7, (value)); break;
        case 8: __RV_CSR_WRITE(CSR_MHPMCOUNTER8, (value)); break;
        case 9: __RV_CSR_WRITE(CSR_MHPMCOUNTER9, (value)); break;
        case 10: __RV_CSR_WRITE(CSR_MHPMCOUNTER10, (value)); break;
        case 11: __RV_CSR_WRITE(CSR_MHPMCOUNTER11, (value)); break;
        case 12: __RV_CSR_WRITE(CSR_MHPMCOUNTER12, (value)); break;
        case 13: __RV_CSR_WRITE(CSR_MHPMCOUNTER13, (value)); break;
        case 14: __RV_CSR_WRITE(CSR_MHPMCOUNTER14, (value)); break;
        case 15: __RV_CSR_WRITE(CSR_MHPMCOUNTER15, (value)); break;
        case 16: __RV_CSR_WRITE(CSR_MHPMCOUNTER16, (value)); break;
        case 17: __RV_CSR_WRITE(CSR_MHPMCOUNTER17, (value)); break;
        case 18: __RV_CSR_WRITE(CSR_MHPMCOUNTER18, (value)); break;
        case 19: __RV_CSR_WRITE(CSR_MHPMCOUNTER19, (value)); break;
        case 20: __RV_CSR_WRITE(CSR_MHPMCOUNTER20, (value)); break;
        case 21: __RV_CSR_WRITE(CSR_MHPMCOUNTER21, (value)); break;
        case 22: __RV_CSR_WRITE(CSR_MHPMCOUNTER22, (value)); break;
        case 23: __RV_CSR_WRITE(CSR_MHPMCOUNTER23, (value)); break;
        case 24: __RV_CSR_WRITE(CSR_MHPMCOUNTER24, (value)); break;
        case 25: __RV_CSR_WRITE(CSR_MHPMCOUNTER25, (value)); break;
        case 26: __RV_CSR_WRITE(CSR_MHPMCOUNTER26, (value)); break;
        case 27: __RV_CSR_WRITE(CSR_MHPMCOUNTER27, (value)); break;
        case 28: __RV_CSR_WRITE(CSR_MHPMCOUNTER28, (value)); break;
        case 29: __RV_CSR_WRITE(CSR_MHPMCOUNTER29, (value)); break;
        case 30: __RV_CSR_WRITE(CSR_MHPMCOUNTER30, (value)); break;
        case 31: __RV_CSR_WRITE(CSR_MHPMCOUNTER31, (value)); break;

#else
#endif
        default: break;
    }
}

/**
 * \brief   Get value of selected high performance monitor counter
 * \param [in]    idx     HPMCOUNTERx CSR index(3-31)
 * \details
 * Get high performance monitor counter register value
 * \return               HPMCOUNTERx Register value
 */
__STATIC_INLINE uint64_t __get_hpm_counter(unsigned long idx)
{
#if __RISCV_XLEN == 32
    volatile uint32_t high0, low, high;
    uint64_t full;

    switch (idx) {
        case 0: return __get_rv_cycle();
        case 2: return __get_rv_instret();
        case 3: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER3H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER3);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER3H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER3); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 4: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER4H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER4);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER4H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER4); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 5: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER5H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER5);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER5H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER5); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 6: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER6H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER6);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER6H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER6); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 7: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER7H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER7);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER7H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER7); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 8: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER8H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER8);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER8H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER8); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 9: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER9H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER9);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER9H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER9); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 10: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER10H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER10);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER10H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER10); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 11: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER11H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER11);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER11H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER11); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 12: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER12H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER12);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER12H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER12); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 13: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER13H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER13);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER13H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER13); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 14: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER14H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER14);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER14H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER14); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 15: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER15H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER15);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER15H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER15); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 16: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER16H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER16);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER16H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER16); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 17: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER17H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER17);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER17H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER17); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 18: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER18H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER18);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER18H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER18); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 19: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER19H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER19);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER19H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER19); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 20: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER20H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER20);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER20H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER20); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 21: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER21H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER21);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER21H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER21); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 22: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER22H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER22);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER22H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER22); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 23: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER23H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER23);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER23H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER23); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 24: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER24H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER24);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER24H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER24); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 25: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER25H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER25);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER25H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER25); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 26: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER26H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER26);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER26H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER26); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 27: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER27H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER27);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER27H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER27); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 28: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER28H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER28);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER28H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER28); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 29: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER29H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER29);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER29H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER29); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 30: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER30H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER30);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER30H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER30); }
            full = (((uint64_t)high) << 32) | low; return full;
        case 31: high0 = __RV_CSR_READ(CSR_MHPMCOUNTER31H);
            low = __RV_CSR_READ(CSR_MHPMCOUNTER31);
            high = __RV_CSR_READ(CSR_MHPMCOUNTER31H);
            if (high0 != high) { low = __RV_CSR_READ(CSR_MHPMCOUNTER31); }
            full = (((uint64_t)high) << 32) | low; return full;

#elif __RISCV_XLEN == 64
    switch (idx) {
        case 0: return __get_rv_cycle();
        case 2: return __get_rv_instret();
        case 3: return __RV_CSR_READ(CSR_MHPMCOUNTER3);
        case 4: return __RV_CSR_READ(CSR_MHPMCOUNTER4);
        case 5: return __RV_CSR_READ(CSR_MHPMCOUNTER5);
        case 6: return __RV_CSR_READ(CSR_MHPMCOUNTER6);
        case 7: return __RV_CSR_READ(CSR_MHPMCOUNTER7);
        case 8: return __RV_CSR_READ(CSR_MHPMCOUNTER8);
        case 9: return __RV_CSR_READ(CSR_MHPMCOUNTER9);
        case 10: return __RV_CSR_READ(CSR_MHPMCOUNTER10);
        case 11: return __RV_CSR_READ(CSR_MHPMCOUNTER11);
        case 12: return __RV_CSR_READ(CSR_MHPMCOUNTER12);
        case 13: return __RV_CSR_READ(CSR_MHPMCOUNTER13);
        case 14: return __RV_CSR_READ(CSR_MHPMCOUNTER14);
        case 15: return __RV_CSR_READ(CSR_MHPMCOUNTER15);
        case 16: return __RV_CSR_READ(CSR_MHPMCOUNTER16);
        case 17: return __RV_CSR_READ(CSR_MHPMCOUNTER17);
        case 18: return __RV_CSR_READ(CSR_MHPMCOUNTER18);
        case 19: return __RV_CSR_READ(CSR_MHPMCOUNTER19);
        case 20: return __RV_CSR_READ(CSR_MHPMCOUNTER20);
        case 21: return __RV_CSR_READ(CSR_MHPMCOUNTER21);
        case 22: return __RV_CSR_READ(CSR_MHPMCOUNTER22);
        case 23: return __RV_CSR_READ(CSR_MHPMCOUNTER23);
        case 24: return __RV_CSR_READ(CSR_MHPMCOUNTER24);
        case 25: return __RV_CSR_READ(CSR_MHPMCOUNTER25);
        case 26: return __RV_CSR_READ(CSR_MHPMCOUNTER26);
        case 27: return __RV_CSR_READ(CSR_MHPMCOUNTER27);
        case 28: return __RV_CSR_READ(CSR_MHPMCOUNTER28);
        case 29: return __RV_CSR_READ(CSR_MHPMCOUNTER29);
        case 30: return __RV_CSR_READ(CSR_MHPMCOUNTER30);
        case 31: return __RV_CSR_READ(CSR_MHPMCOUNTER31);

#else
    switch (idx) {
#endif
        default: return 0;
    }
}

/**
 * \brief   Get value of selected high performance monitor counter
 * \param [in]    idx     HPMCOUNTERx CSR index(3-31)
 * \details
 * Get high performance monitor counter register value without high
 *          32 bits when XLEN=32
 * \return               HPMCOUNTERx Register value
 */
__STATIC_INLINE unsigned long __read_hpm_counter(unsigned long idx)
{
    switch (idx) {
        case 0: return __read_cycle_csr();
        case 2: return __read_instret_csr();
        case 3: return __RV_CSR_READ(CSR_MHPMCOUNTER3);
        case 4: return __RV_CSR_READ(CSR_MHPMCOUNTER4);
        case 5: return __RV_CSR_READ(CSR_MHPMCOUNTER5);
        case 6: return __RV_CSR_READ(CSR_MHPMCOUNTER6);
        case 7: return __RV_CSR_READ(CSR_MHPMCOUNTER7);
        case 8: return __RV_CSR_READ(CSR_MHPMCOUNTER8);
        case 9: return __RV_CSR_READ(CSR_MHPMCOUNTER9);
        case 10: return __RV_CSR_READ(CSR_MHPMCOUNTER10);
        case 11: return __RV_CSR_READ(CSR_MHPMCOUNTER11);
        case 12: return __RV_CSR_READ(CSR_MHPMCOUNTER12);
        case 13: return __RV_CSR_READ(CSR_MHPMCOUNTER13);
        case 14: return __RV_CSR_READ(CSR_MHPMCOUNTER14);
        case 15: return __RV_CSR_READ(CSR_MHPMCOUNTER15);
        case 16: return __RV_CSR_READ(CSR_MHPMCOUNTER16);
        case 17: return __RV_CSR_READ(CSR_MHPMCOUNTER17);
        case 18: return __RV_CSR_READ(CSR_MHPMCOUNTER18);
        case 19: return __RV_CSR_READ(CSR_MHPMCOUNTER19);
        case 20: return __RV_CSR_READ(CSR_MHPMCOUNTER20);
        case 21: return __RV_CSR_READ(CSR_MHPMCOUNTER21);
        case 22: return __RV_CSR_READ(CSR_MHPMCOUNTER22);
        case 23: return __RV_CSR_READ(CSR_MHPMCOUNTER23);
        case 24: return __RV_CSR_READ(CSR_MHPMCOUNTER24);
        case 25: return __RV_CSR_READ(CSR_MHPMCOUNTER25);
        case 26: return __RV_CSR_READ(CSR_MHPMCOUNTER26);
        case 27: return __RV_CSR_READ(CSR_MHPMCOUNTER27);
        case 28: return __RV_CSR_READ(CSR_MHPMCOUNTER28);
        case 29: return __RV_CSR_READ(CSR_MHPMCOUNTER29);
        case 30: return __RV_CSR_READ(CSR_MHPMCOUNTER30);
        case 31: return __RV_CSR_READ(CSR_MHPMCOUNTER31);
        default: return 0;
    }
}

/**
 * \brief   Set exceptions delegation to S mode
 * \details Set certain exceptions of supervisor mode or user mode
 *          delegated from machined mode to supervisor mode.
 * \remarks
 *          Exception should trigger in supervisor mode or user mode.
 */
__STATIC_FORCEINLINE void __set_medeleg(unsigned long mask)
{
    __RV_CSR_WRITE(CSR_MEDELEG, mask);
}

/**
 * \brief   Set interrupt delegation to S mode
 * \details Set certain interrupt of supervisor mode or user mode
 *          delegated from machined mode to supervisor mode.
 * \remarks
 *          interrupt should trigger in supervisor mode or user mode.
 */
__STATIC_FORCEINLINE void __set_mideleg(unsigned long mask)
{
    __RV_CSR_WRITE(CSR_MIDELEG, mask);
}

/**
 * \brief Execute fence instruction, p -> pred, s -> succ
 * \details
 * the FENCE instruction ensures that all memory accesses from instructions preceding
 * the fence in program order (the `predecessor set`) appear earlier in the global memory order than
 * memory accesses from instructions appearing after the fence in program order (the `successor set`).
 * For details, please refer to The RISC-V Instruction Set Manual
 * \param p     predecessor set, such as iorw, rw, r, w
 * \param s     successor set, such as iorw, rw, r, w
 **/
#define __FENCE(p, s) __ASM volatile ("fence " #p "," #s : : : "memory")

/**
 * \brief   Fence.i Instruction
 * \details
 * The FENCE.I instruction is used to synchronize the instruction
 * and data streams.
 */
__STATIC_FORCEINLINE void __FENCE_I(void)
{
    __ASM volatile("fence.i");
}

/** \brief Read & Write Memory barrier */
#define __RWMB()        __FENCE(iorw,iorw)

/** \brief Read Memory barrier */
#define __RMB()         __FENCE(ir,ir)

/** \brief Write Memory barrier */
#define __WMB()         __FENCE(ow,ow)

/** \brief SMP Read & Write Memory barrier */
#define __SMP_RWMB()    __FENCE(rw,rw)

/** \brief SMP Read Memory barrier */
#define __SMP_RMB()     __FENCE(r,r)

/** \brief SMP Write Memory barrier */
#define __SMP_WMB()     __FENCE(w,w)

/** \brief CPU relax for busy loop */
#define __CPU_RELAX()   __ASM volatile ("" : : : "memory")


/* ===== Load/Store Operations ===== */
/**
 * \brief  Load 8bit value from address (8 bit)
 * \details Load 8 bit value.
 * \param [in]    addr  Address pointer to data
 * \return              value of type uint8_t at (*addr)
 */
__STATIC_FORCEINLINE uint8_t __LB(volatile void *addr)
{
    uint8_t result;

    __ASM volatile ("lb %0, 0(%1)" : "=r" (result) : "r" (addr));
    return result;
}

/**
 * \brief  Load 16bit value from address (16 bit)
 * \details Load 16 bit value.
 * \param [in]    addr  Address pointer to data
 * \return              value of type uint16_t at (*addr)
 */
__STATIC_FORCEINLINE uint16_t __LH(volatile void *addr)
{
    uint16_t result;

    __ASM volatile ("lh %0, 0(%1)" : "=r" (result) : "r" (addr));
    return result;
}

/**
 * \brief  Load 32bit value from address (32 bit)
 * \details Load 32 bit value.
 * \param [in]    addr  Address pointer to data
 * \return              value of type uint32_t at (*addr)
 */
__STATIC_FORCEINLINE uint32_t __LW(volatile void *addr)
{
    uint32_t result;

    __ASM volatile ("lw %0, 0(%1)" : "=r" (result) : "r" (addr));
    return result;
}

#if __RISCV_XLEN != 32
/**
 * \brief  Load 64bit value from address (64 bit)
 * \details Load 64 bit value.
 * \param [in]    addr  Address pointer to data
 * \return              value of type uint64_t at (*addr)
 * \remarks RV64 only macro
 */
__STATIC_FORCEINLINE uint64_t __LD(volatile void *addr)
{
    uint64_t result;
    __ASM volatile ("ld %0, 0(%1)" : "=r" (result) : "r" (addr));
    return result;
}
#endif

/**
 * \brief  Write 8bit value to address (8 bit)
 * \details Write 8 bit value.
 * \param [in]    addr  Address pointer to data
 * \param [in]    val   Value to set
 */
__STATIC_FORCEINLINE void __SB(volatile void *addr, uint8_t val)
{
    __ASM volatile ("sb %0, 0(%1)" : : "r" (val), "r" (addr));
}

/**
 * \brief  Write 16bit value to address (16 bit)
 * \details Write 16 bit value.
 * \param [in]    addr  Address pointer to data
 * \param [in]    val   Value to set
 */
__STATIC_FORCEINLINE void __SH(volatile void *addr, uint16_t val)
{
    __ASM volatile ("sh %0, 0(%1)" : : "r" (val), "r" (addr));
}

/**
 * \brief  Write 32bit value to address (32 bit)
 * \details Write 32 bit value.
 * \param [in]    addr  Address pointer to data
 * \param [in]    val   Value to set
 */
__STATIC_FORCEINLINE void __SW(volatile void *addr, uint32_t val)
{
    __ASM volatile ("sw %0, 0(%1)" : : "r" (val), "r" (addr));
}

#if __RISCV_XLEN != 32
/**
 * \brief  Write 64bit value to address (64 bit)
 * \details Write 64 bit value.
 * \param [in]    addr  Address pointer to data
 * \param [in]    val   Value to set
 */
__STATIC_FORCEINLINE void __SD(volatile void *addr, uint64_t val)
{
    __ASM volatile ("sd %0, 0(%1)" : : "r" (val), "r" (addr));
}
#endif

/**
 * \brief  Compare and Swap 32bit value using LR and SC
 * \details Compare old value with memory, if identical,
 * store new value in memory. Return the initial value in memory.
 * Success is indicated by comparing return value with OLD.
 * memory address, return 0 if successful, otherwise return !0
 * \param [in]    addr      Address pointer to data, address need to be 4byte aligned
 * \param [in]    oldval    Old value of the data in address
 * \param [in]    newval    New value to be stored into the address
 * \return  return the initial value in memory
 */
__STATIC_INLINE uint32_t __CAS_W(volatile uint32_t *addr, uint32_t oldval, uint32_t newval)
{
    uint32_t result;
    uint32_t rc;

    __ASM volatile (                                \
            "0:     lr.w %0, %2      \n"            \
            "       bne  %0, %z3, 1f \n"            \
            "       sc.w %1, %z4, %2 \n"            \
            "       bnez %1, 0b      \n"            \
            "1:\n"                                  \
            : "=&r"(result), "=&r"(rc), "+A"(*addr) \
            : "r"(oldval), "r"(newval)              \
            : "memory");
    return result;
}

/**
 * \brief  Atomic Swap 32bit value into memory
 * \details Atomically swap new 32bit value into memory using amoswap.d.
 * \param [in]    addr      Address pointer to data, address need to be 4byte aligned
 * \param [in]    newval    New value to be stored into the address
 * \return  return the original value in memory
 */
__STATIC_FORCEINLINE uint32_t __AMOSWAP_W(volatile uint32_t *addr, uint32_t newval)
{
    uint32_t result;

    __ASM volatile ("amoswap.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(newval) : "memory");
    return result;
}

/**
 * \brief  Atomic Add with 32bit value
 * \details Atomically ADD 32bit value with value in memory using amoadd.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be ADDed
 * \return  return memory value + add value
 */
__STATIC_FORCEINLINE int32_t __AMOADD_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amoadd.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic And with 32bit value
 * \details Atomically AND 32bit value with value in memory using amoand.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be ANDed
 * \return  return memory value & and value
 */
__STATIC_FORCEINLINE int32_t __AMOAND_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amoand.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic OR with 32bit value
 * \details Atomically OR 32bit value with value in memory using amoor.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be ORed
 * \return  return memory value | and value
 */
__STATIC_FORCEINLINE int32_t __AMOOR_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amoor.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic XOR with 32bit value
 * \details Atomically XOR 32bit value with value in memory using amoxor.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be XORed
 * \return  return memory value ^ and value
 */
__STATIC_FORCEINLINE int32_t __AMOXOR_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amoxor.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic unsigned MAX with 32bit value
 * \details Atomically unsigned max compare 32bit value with value in memory using amomaxu.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be compared
 * \return  return the bigger value
 */
__STATIC_FORCEINLINE uint32_t __AMOMAXU_W(volatile uint32_t *addr, uint32_t value)
{
    uint32_t result;

    __ASM volatile ("amomaxu.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic signed MAX with 32bit value
 * \details Atomically signed max compare 32bit value with value in memory using amomax.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be compared
 * \return the bigger value
 */
__STATIC_FORCEINLINE int32_t __AMOMAX_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amomax.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic unsigned MIN with 32bit value
 * \details Atomically unsigned min compare 32bit value with value in memory using amominu.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be compared
 * \return the smaller value
 */
__STATIC_FORCEINLINE uint32_t __AMOMINU_W(volatile uint32_t *addr, uint32_t value)
{
    uint32_t result;

    __ASM volatile ("amominu.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic signed MIN with 32bit value
 * \details Atomically signed min compare 32bit value with value in memory using amomin.d.
 * \param [in]    addr   Address pointer to data, address need to be 4byte aligned
 * \param [in]    value  value to be compared
 * \return  the smaller value
 */
__STATIC_FORCEINLINE int32_t __AMOMIN_W(volatile int32_t *addr, int32_t value)
{
    int32_t result;

    __ASM volatile ("amomin.w %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

#if __RISCV_XLEN == 64
/**
 * \brief  Compare and Swap 64bit value using LR and SC
 * \details Compare old value with memory, if identical,
 * store new value in memory. Return the initial value in memory.
 * Success is indicated by comparing return value with OLD.
 * memory address, return 0 if successful, otherwise return !0
 * \param [in]    addr      Address pointer to data, address need to be 8byte aligned
 * \param [in]    oldval    Old value of the data in address
 * \param [in]    newval    New value to be stored into the address
 * \return  return the initial value in memory
 */
__STATIC_INLINE uint64_t __CAS_D(volatile uint64_t *addr, uint64_t oldval, uint64_t newval)
{
    uint64_t result;
    uint64_t rc;

    __ASM volatile (                                \
            "0:     lr.d %0, %2      \n"            \
            "       bne  %0, %z3, 1f \n"            \
            "       sc.d %1, %z4, %2 \n"            \
            "       bnez %1, 0b      \n"            \
            "1:\n"                                  \
            : "=&r"(result), "=&r"(rc), "+A"(*addr) \
            : "r"(oldval), "r"(newval)              \
            : "memory");
    return result;
}

/**
 * \brief  Atomic Swap 64bit value into memory
 * \details Atomically swap new 64bit value into memory using amoswap.d.
 * \param [in]    addr      Address pointer to data, address need to be 8byte aligned
 * \param [in]    newval    New value to be stored into the address
 * \return  return the original value in memory
 */
__STATIC_FORCEINLINE uint64_t __AMOSWAP_D(volatile uint64_t *addr, uint64_t newval)
{
    uint64_t result;

    __ASM volatile ("amoswap.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(newval) : "memory");
    return result;
}

/**
 * \brief  Atomic Add with 64bit value
 * \details Atomically ADD 64bit value with value in memory using amoadd.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be ADDed
 * \return  return memory value + add value
 */
__STATIC_FORCEINLINE int64_t __AMOADD_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amoadd.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic And with 64bit value
 * \details Atomically AND 64bit value with value in memory using amoand.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be ANDed
 * \return  return memory value & and value
 */
__STATIC_FORCEINLINE int64_t __AMOAND_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amoand.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic OR with 64bit value
 * \details Atomically OR 64bit value with value in memory using amoor.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be ORed
 * \return  return memory value | and value
 */
__STATIC_FORCEINLINE int64_t __AMOOR_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amoor.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic XOR with 64bit value
 * \details Atomically XOR 64bit value with value in memory using amoxor.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be XORed
 * \return  return memory value ^ and value
 */
__STATIC_FORCEINLINE int64_t __AMOXOR_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amoxor.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic unsigned MAX with 64bit value
 * \details Atomically unsigned max compare 64bit value with value in memory using amomaxu.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be compared
 * \return  return the bigger value
 */
__STATIC_FORCEINLINE uint64_t __AMOMAXU_D(volatile uint64_t *addr, uint64_t value)
{
    uint64_t result;

    __ASM volatile ("amomaxu.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic signed MAX with 64bit value
 * \details Atomically signed max compare 64bit value with value in memory using amomax.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be compared
 * \return the bigger value
 */
__STATIC_FORCEINLINE int64_t __AMOMAX_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amomax.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic unsigned MIN with 64bit value
 * \details Atomically unsigned min compare 64bit value with value in memory using amominu.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be compared
 * \return the smaller value
 */
__STATIC_FORCEINLINE uint64_t __AMOMINU_D(volatile uint64_t *addr, uint64_t value)
{
    uint64_t result;

    __ASM volatile ("amominu.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}

/**
 * \brief  Atomic signed MIN with 64bit value
 * \details Atomically signed min compare 64bit value with value in memory using amomin.d.
 * \param [in]    addr   Address pointer to data, address need to be 8byte aligned
 * \param [in]    value  value to be compared
 * \return  the smaller value
 */
__STATIC_FORCEINLINE int64_t __AMOMIN_D(volatile int64_t *addr, int64_t value)
{
    int64_t result;

    __ASM volatile ("amomin.d %0, %2, %1" : \
            "=r"(result), "+A"(*addr) : "r"(value) : "memory");
    return *addr;
}
#endif /* __RISCV_XLEN == 64  */

/** @} */ /* End of Doxygen Group NMSIS_Core_CPU_Intrinsic */

#ifdef __cplusplus
}
#endif
#endif /* __CORE_FEATURE_BASE__ */
