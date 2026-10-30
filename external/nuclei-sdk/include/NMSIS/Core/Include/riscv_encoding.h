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
#ifndef __RISCV_ENCODING_H__
#define __RISCV_ENCODING_H__

#ifdef __cplusplus
 extern "C" {
#endif

#include "riscv_bits.h"

/**
 * \defgroup NMSIS_Core_CSR_Encoding    Core CSR Encodings
 * \ingroup  NMSIS_Core
 * \brief    NMSIS Core CSR Encodings
 * \details
 *
 * The following macros are used for CSR encodings
 *   @{
 */
/* === Standard CSR bit mask === */
#define MSTATUS_UIE         0x00000001
#define MSTATUS_SIE         0x00000002
#define MSTATUS_HIE         0x00000004
#define MSTATUS_MIE         0x00000008
#define MSTATUS_UPIE        0x00000010
#define MSTATUS_SPIE        0x00000020
#define MSTATUS_UBE         0x00000040
#define MSTATUS_MPIE        0x00000080
#define MSTATUS_SPP         0x00000100
#define MSTATUS_VS          0x00000600
#define MSTATUS_MPP         0x00001800
#define MSTATUS_FS          0x00006000
#define MSTATUS_XS          0x00018000
#define MSTATUS_MPRV        0x00020000
#define MSTATUS_SUM         0x00040000
#define MSTATUS_MXR         0x00080000
#define MSTATUS_TVM         0x00100000
#define MSTATUS_TW          0x00200000
#define MSTATUS_TSR         0x00400000
#define MSTATUS32_SD        0x80000000
#define MSTATUS_UXL         0x0000000300000000
#define MSTATUS_SXL         0x0000000C00000000
#define MSTATUS_SBE         0x0000001000000000
#define MSTATUS_MBE         0x0000002000000000
#define MSTATUS_GVA         0x0000004000000000
#define MSTATUS_MPV         0x0000008000000000
#define MSTATUS64_SD        0x8000000000000000

#define MSTATUS_FS_INITIAL  0x00002000
#define MSTATUS_FS_CLEAN    0x00004000
#define MSTATUS_FS_DIRTY    0x00006000

#define MSTATUS_VS_INITIAL  0x00000200
#define MSTATUS_VS_CLEAN    0x00000400
#define MSTATUS_VS_DIRTY    0x00000600

#define MSTATUSH_SBE        0x00000010
#define MSTATUSH_MBE        0x00000020
#define MSTATUSH_GVA        0x00000040
#define MSTATUSH_MPV        0x00000080

#define SSTATUS_UIE         0x00000001
#define SSTATUS_SIE         0x00000002
#define SSTATUS_UPIE        0x00000010
#define SSTATUS_SPIE        0x00000020
#define SSTATUS_UBE         0x00000040
#define SSTATUS_SPP         0x00000100
#define SSTATUS_VS          0x00000600
#define SSTATUS_FS          0x00006000
#define SSTATUS_XS          0x00018000
#define SSTATUS_SUM         0x00040000
#define SSTATUS_MXR         0x00080000
#define SSTATUS32_SD        0x80000000
#define SSTATUS_UXL         0x0000000300000000
#define SSTATUS64_SD        0x8000000000000000

#define USTATUS_UIE         0x00000001
#define USTATUS_UPIE        0x00000010

#define DCSR_XDEBUGVER      (3U<<30)
#define DCSR_NDRESET        (1<<29)
#define DCSR_FULLRESET      (1<<28)
#define DCSR_EBREAKM        (1<<15)
#define DCSR_EBREAKH        (1<<14)
#define DCSR_EBREAKS        (1<<13)
#define DCSR_EBREAKU        (1<<12)
#define DCSR_STOPCYCLE      (1<<10)
#define DCSR_STOPTIME       (1<<9)
#define DCSR_CAUSE          (7<<6)
#define DCSR_DEBUGINT       (1<<5)
#define DCSR_HALT           (1<<3)
#define DCSR_STEP           (1<<2)
#define DCSR_PRV            (3<<0)

#define DCSR_CAUSE_NONE     0
#define DCSR_CAUSE_SWBP     1
#define DCSR_CAUSE_HWBP     2
#define DCSR_CAUSE_DEBUGINT 3
#define DCSR_CAUSE_STEP     4
#define DCSR_CAUSE_HALT     5

#define MCONTROL_TYPE(xlen)    (0xfULL<<((xlen)-4))
#define MCONTROL_DMODE(xlen)   (1ULL<<((xlen)-5))
#define MCONTROL_MASKMAX(xlen) (0x3fULL<<((xlen)-11))

#define MCONTROL_SELECT     (1<<19)
#define MCONTROL_TIMING     (1<<18)
#define MCONTROL_ACTION     (0x3f<<12)
#define MCONTROL_CHAIN      (1<<11)
#define MCONTROL_MATCH      (0xf<<7)
#define MCONTROL_M          (1<<6)
#define MCONTROL_H          (1<<5)
#define MCONTROL_S          (1<<4)
#define MCONTROL_U          (1<<3)
#define MCONTROL_EXECUTE    (1<<2)
#define MCONTROL_STORE      (1<<1)
#define MCONTROL_LOAD       (1<<0)

#define MCONTROL_TYPE_NONE      0
#define MCONTROL_TYPE_MATCH     2

#define MCONTROL_ACTION_DEBUG_EXCEPTION   0
#define MCONTROL_ACTION_DEBUG_MODE        1
#define MCONTROL_ACTION_TRACE_START       2
#define MCONTROL_ACTION_TRACE_STOP        3
#define MCONTROL_ACTION_TRACE_EMIT        4

#define MCONTROL_MATCH_EQUAL     0
#define MCONTROL_MATCH_NAPOT     1
#define MCONTROL_MATCH_GE        2
#define MCONTROL_MATCH_LT        3
#define MCONTROL_MATCH_MASK_LOW  4
#define MCONTROL_MATCH_MASK_HIGH 5

#define MIP_SSIP            (1 << IRQ_S_SOFT)
#define MIP_HSIP            (1 << IRQ_H_SOFT)
#define MIP_MSIP            (1 << IRQ_M_SOFT)
#define MIP_STIP            (1 << IRQ_S_TIMER)
#define MIP_HTIP            (1 << IRQ_H_TIMER)
#define MIP_MTIP            (1 << IRQ_M_TIMER)
#define MIP_SEIP            (1 << IRQ_S_EXT)
#define MIP_HEIP            (1 << IRQ_H_EXT)
#define MIP_MEIP            (1 << IRQ_M_EXT)

#define MIE_SSIE            MIP_SSIP
#define MIE_HSIE            MIP_HSIP
#define MIE_MSIE            MIP_MSIP
#define MIE_STIE            MIP_STIP
#define MIE_HTIE            MIP_HTIP
#define MIE_MTIE            MIP_MTIP
#define MIE_SEIE            MIP_SEIP
#define MIE_HEIE            MIP_HEIP
#define MIE_MEIE            MIP_MEIP

#define SIP_SSIP            MIP_SSIP
#define SIP_STIP            MIP_STIP
#define SIP_SEIP            MIP_SEIP

#define SIE_SSIE            MIP_SSIP
#define SIE_STIE            MIP_STIP
#define SIE_SEIE            MIP_SEIP

#define MCAUSE_INTR         (1ULL << (__riscv_xlen - 1))
#define MCAUSE_CAUSE        0x00000FFFUL
#define SCAUSE_INTR         MCAUSE_INTR
#define SCAUSE_CAUSE        0x000003FFUL

#define MENVCFG_CBIE_EN     (0x11 << 4)
#define MENVCFG_CBIE_FLUSH  (0x01 << 4)
#define MENVCFG_CBIE_INVAL  (0x11 << 4)
#define SENVCFG_CBIE_EN     (0x11 << 4)
#define SENVCFG_CBIE_FLUSH  (0x01 << 4)
#define SENVCFG_CBIE_INVAL  (0x11 << 4)

#define MENVCFG_FIOM        0x00000001
#define MENVCFG_LPE         0x00000004
#define MENVCFG_SSE         0x00000008
#define MENVCFG_CBIE        0x00000030
#define MENVCFG_CBCFE       0x00000040
#define MENVCFG_CBZE        0x00000080
#define MENVCFG_PMM         0x0000000300000000
#define MENVCFG_DTE         0x0800000000000000
#define MENVCFG_ADUE        0x2000000000000000
#define MENVCFG_PBMTE       0x4000000000000000
#define MENVCFG_STCE        0x8000000000000000

#define MENVCFGH_DTE        0x08000000
#define MENVCFGH_ADUE       0x20000000
#define MENVCFGH_PBMTE      0x40000000
#define MENVCFGH_STCE       0x80000000

#define SENVCFG_FIOM        0x00000001
#define SENVCFG_LPE         0x00000004
#define SENVCFG_SSE         0x00000008
#define SENVCFG_CBIE        0x00000030
#define SENVCFG_CBCFE       0x00000040
#define SENVCFG_CBZE        0x00000080
#define SENVCFG_PMM         0x0000000300000000

/* === P-ext CSR bit mask === */

#define UCODE_OV            (0x1)

/* === Nuclei custom CSR bit mask === */
#define CSR_MCACHE_CTL_IE               0x00000001
#define CSR_MCACHE_CTL_DE               0x00010000

#define WFE_WFE                     (0x1)
#define TXEVT_TXEVT                 (0x1)
#define SLEEPVALUE_SLEEPVALUE       (0x1)

#define MCOUNTEREN_CY_SHIFT         0
#define MCOUNTEREN_TIME_SHIFT       1
#define MCOUNTEREN_IR_SHIFT         2

#define MCOUNTEREN_CY               (1U << MCOUNTEREN_CY_SHIFT)
#define MCOUNTEREN_TIME             (1U << MCOUNTEREN_TIME_SHIFT)
#define MCOUNTEREN_IR               (1U << MCOUNTEREN_IR_SHIFT)

#define MCOUNTINHIBIT_CY            MCOUNTEREN_CY
#define MCOUNTINHIBIT_IR            MCOUNTEREN_IR

#define MILM_CTL_ILM_BPA            (((1ULL<<((__riscv_xlen)-10))-1)<<10)
#define MILM_CTL_ILM_ECC_CHK_EN     (1<<4)
#define MILM_CTL_ILM_RWECC          (1<<3)
#define MILM_CTL_ILM_ECC_INJ_EN     (1<<3)
#define MILM_CTL_ILM_ECC_EXCP_EN    (1<<2)
#define MILM_CTL_ILM_ECC_EN         (1<<1)
#define MILM_CTL_ILM_EN             (1<<0)

#define MDLM_CTL_DLM_BPA            (((1ULL<<((__riscv_xlen)-10))-1)<<10)
#define MDLM_CTL_DLM_ECC_CHK_EN     (1<<4)
#define MDLM_CTL_DLM_RWECC          (1<<3)
#define MDLM_CTL_DLM_ECC_INJ_EN     (1<<3)
#define MDLM_CTL_DLM_ECC_EXCP_EN    (1<<2)
#define MDLM_CTL_DLM_ECC_EN         (1<<1)
#define MDLM_CTL_DLM_EN             (1<<0)

#define MSUBM_PTYP                  (0x3<<8)
#define MSUBM_TYP                   (0x3<<6)

#define MDCAUSE_MDCAUSE             (0x7)

#define MMISC_CTL_LDSPEC_ENABLE     (1<<12)
#define MMISC_CTL_SIJUMP_ENABLE     (1<<11)
#define MMISC_CTL_IMRETURN_ENABLE   (1<<10)
#define MMISC_CTL_NMI_CAUSE_FFF     (1<<9)
#define MMISC_CTL_CODE_BUS_ERR      (1<<8)
#define MMISC_CTL_MISALIGN          (1<<6)
#define MMISC_CTL_ZC                (1<<7)
#define MMISC_CTL_BPU               (1<<3)

#define MCACHE_CTL_IC_EN            (1<<0)
#define MCACHE_CTL_IC_SCPD_MOD      (1<<1)
#define MCACHE_CTL_IC_ECC_EN        (1<<2)
#define MCACHE_CTL_IC_ECC_EXCP_EN   (1<<3)
#define MCACHE_CTL_IC_TRAM_ECC_INJ_EN   (1<<4)
#define MCACHE_CTL_IC_RWTECC        (1<<4)
#define MCACHE_CTL_IC_RWDECC        (1<<5)
#define MCACHE_CTL_IC_DRAM_ECC_INJ_EN   (1<<5)
#define MCACHE_CTL_IC_PF_EN         (1<<6)
#define MCACHE_CTL_IC_CANCEL_EN     (1<<7)
#define MCACHE_CTL_IC_ECC_CHK_EN    (1<<8)
#define MCACHE_CTL_DC_EN            (1<<16)
#define MCACHE_CTL_DC_ECC_EN        (1<<17)
#define MCACHE_CTL_DC_ECC_EXCP_EN   (1<<18)
#define MCACHE_CTL_DC_TRAM_ECC_INJ_EN   (1<<19)
#define MCACHE_CTL_DC_RWTECC        (1<<19)
#define MCACHE_CTL_DC_RWDECC        (1<<20)
#define MCACHE_CTL_DC_DRAM_ECC_INJ_EN   (1<<20)
#define MCACHE_CTL_DC_ECC_CHK_EN    (1<<21)

#define MTVT2_MTVT2EN               (1<<0)
#define MTVT2_COMMON_CODE_ENTRY     (((1ULL<<((__riscv_xlen)-2))-1)<<2)

#define MCFG_INFO_TEE               (1<<0)
#define MCFG_INFO_ECC               (1<<1)
#define MCFG_INFO_CLIC              (1<<2)
#define MCFG_INFO_PLIC              (1<<3)
#define MCFG_INFO_FIO               (1<<4)
#define MCFG_INFO_PPI               (1<<5)
#define MCFG_INFO_NICE              (1<<6)
#define MCFG_INFO_ILM               (1<<7)
#define MCFG_INFO_DLM               (1<<8)
#define MCFG_INFO_ICACHE            (1<<9)
#define MCFG_INFO_DCACHE            (1<<10)
#define MCFG_INFO_SMP               (1<<11)
#define MCFG_INFO_DSP_N1            (1<<12)
#define MCFG_INFO_DSP_N2            (1<<13)
#define MCFG_INFO_DSP_N3            (1<<14)
#define MCFG_INFO_IREGION_EXIST     (1<<16)
#define MCFG_INFO_VP                (0x3<<17)

#define MICFG_IC_SET                (0xF<<0)
#define MICFG_IC_WAY                (0x7<<4)
#define MICFG_IC_LSIZE              (0x7<<7)
#define MICFG_IC_ECC                (0x1<<10)
#define MICFG_ILM_SIZE              (0x1F<<16)
#define MICFG_ILM_XONLY             (0x1<<21)
#define MICFG_ILM_ECC               (0x1<<22)

#define MDCFG_DC_SET                (0xF<<0)
#define MDCFG_DC_WAY                (0x7<<4)
#define MDCFG_DC_LSIZE              (0x7<<7)
#define MDCFG_DC_ECC                (0x1<<10)
#define MDCFG_DLM_SIZE              (0x1F<<16)
#define MDCFG_DLM_ECC               (0x1<<21)

#define MIRGB_INFO_IRG_BASE_ADDR_BOFS       (10)
#define MIRGB_INFO_IREGION_SIZE_BOFS        (1)

#define MPPICFG_INFO_PPI_SIZE       (0x1F<<1)
#define MPPICFG_INFO_PPI_BPA        (((1ULL<<((__riscv_xlen)-10))-1)<<10)

#define MFIOCFG_INFO_FIO_SIZE       (0x1F<<1)
#define MFIOCFG_INFO_FIO_BPA        (((1ULL<<((__riscv_xlen)-10))-1)<<10)

#define MECC_LOCK_ECC_LOCK          (0x1)

#define MECC_CODE_CODE              (0x1FF)
#define MECC_CODE_RAMID             (0x1F<<16)
#define MECC_CODE_SRAMID            (0x1F<<24)

#define CCM_SUEN_SUEN               (0x1<<0)
#define CCM_DATA_DATA               (0x7<<0)
#define CCM_COMMAND_COMMAND         (0x1F<<0)

/* IREGION Offsets */
#define IREGION_IINFO_OFS           (0x0)
#define IREGION_DEBUG_OFS           (0x10000)
#define IREGION_ECLIC_OFS           (0x20000)
#define IREGION_TIMER_OFS           (0x30000)
#define IREGION_SMP_OFS             (0x40000)
#define IREGION_IDU_OFS             (0x50000)
#define IREGION_PL2_OFS             (0x60000)
#define IREGION_DPREFETCH_OFS       (0x70000)
#define IREGION_PLIC_OFS            (0x4000000)

/* === Stack protect === */
#define MSTACK_CTRL_MODE            (0x1<<2)
#define MSTACK_CTRL_UDF_EN          (0x1<<1)
#define MSTACK_CTRL_OVF_TRACK_EN    (0x1)

#define SIP_SSIP MIP_SSIP
#define SIP_STIP MIP_STIP

#define PRV_U 0
#define PRV_S 1
#define PRV_H 2
#define PRV_M 3

#define VM_MBARE 0
#define VM_MBB   1
#define VM_MBBID 2
#define VM_SV32  8
#define VM_SV39  9
#define VM_SV48  10

#define SATP32_MODE 0x80000000
#define SATP32_ASID 0x7FC00000
#define SATP32_PPN  0x003FFFFF
#define SATP64_MODE 0xF000000000000000
#define SATP64_ASID 0x0FFFF00000000000
#define SATP64_PPN  0x00000FFFFFFFFFFF

#define SATP_MODE_OFF  0
#define SATP_MODE_SV32 1
#define SATP_MODE_SV39 8
#define SATP_MODE_SV48 9
#define SATP_MODE_SV57 10
#define SATP_MODE_SV64 11

#define IRQ_S_SOFT   1
#define IRQ_H_SOFT   2
#define IRQ_M_SOFT   3
#define IRQ_S_TIMER  5
#define IRQ_H_TIMER  6
#define IRQ_M_TIMER  7
#define IRQ_S_EXT    9
#define IRQ_H_EXT    10
#define IRQ_M_EXT    11
#define IRQ_COP      12
#define IRQ_HOST     13


/* === FPU FRM Rounding Mode === */
/** FPU Round to Nearest, ties to Even */
#define FRM_RNDMODE_RNE     0x0
/** FPU Round Towards Zero */
#define FRM_RNDMODE_RTZ     0x1
/** FPU Round Down (towards -inf) */
#define FRM_RNDMODE_RDN     0x2
/** FPU Round Up (towards +inf) */
#define FRM_RNDMODE_RUP     0x3
/** FPU Round to nearest, ties to Max Magnitude */
#define FRM_RNDMODE_RMM     0x4
/**
 * In instruction's rm, selects dynamic rounding mode.
 * In Rounding Mode register, Invalid */
#define FRM_RNDMODE_DYN     0x7

/* === FPU FFLAGS Accrued Exceptions === */
/** FPU Inexact */
#define FFLAGS_AE_NX        (1<<0)
/** FPU Underflow */
#define FFLAGS_AE_UF        (1<<1)
/** FPU Overflow */
#define FFLAGS_AE_OF        (1<<2)
/** FPU Divide by Zero */
#define FFLAGS_AE_DZ        (1<<3)
/** FPU Invalid Operation */
#define FFLAGS_AE_NV        (1<<4)

/** Floating Point Register f0-f31, eg. f0 -> FREG(0) */
#define FREG(idx)           f##idx


/* === PMP CFG Bits === */
#define PMP_R                0x01
#define PMP_W                0x02
#define PMP_X                0x04
#define PMP_A                0x18
#define PMP_A_TOR            0x08
#define PMP_A_NA4            0x10
#define PMP_A_NAPOT          0x18
#define PMP_L                0x80

#define PMP_SHIFT            2
#define PMP_COUNT            16

/* === sPMP CFG Bits === */
#define SPMP_R               PMP_R
#define SPMP_W               PMP_W
#define SPMP_X               PMP_X
#define SPMP_A               PMP_A
#define SPMP_A_TOR           PMP_A_TOR
#define SPMP_A_NA4           PMP_A_NA4
#define SPMP_A_NAPOT         PMP_A_NAPOT
#define SPMP_U               0x40
#define SPMP_L               PMP_L

#define SPMP_SHIFT           PMP_SHIFT
#define SPMP_COUNT           16

/* === SMPU CFG Bits === */
#define SMPU_R               SPMP_R
#define SMPU_W               SPMP_W
#define SMPU_X               SPMP_X
#define SMPU_A               SPMP_A
#define SMPU_A_TOR           SPMP_A_TOR
#define SMPU_A_NA4           SPMP_A_NA4
#define SMPU_A_NAPOT         SPMP_A_NAPOT
#define SMPU_S               0x80

#define SMPU_SHIFT           PMP_SHIFT

// page table entry (PTE) fields
#define PTE_V     0x001 // Valid
#define PTE_R     0x002 // Read
#define PTE_W     0x004 // Write
#define PTE_X     0x008 // Execute
#define PTE_U     0x010 // User
#define PTE_G     0x020 // Global
#define PTE_A     0x040 // Accessed
#define PTE_D     0x080 // Dirty
#define PTE_SOFT  0x300 // Reserved for Software

#define PTE_PPN_SHIFT 10

#define PTE_TABLE(PTE) (((PTE) & (PTE_V | PTE_R | PTE_W | PTE_X)) == PTE_V)

#ifdef __riscv

#ifdef __riscv64
# define MSTATUS_SD MSTATUS64_SD
# define SSTATUS_SD SSTATUS64_SD
# define RISCV_PGLEVEL_BITS 9
#else
# define MSTATUS_SD MSTATUS32_SD
# define SSTATUS_SD SSTATUS32_SD
# define RISCV_PGLEVEL_BITS 10
#endif /* __riscv64 */

#define RISCV_PGSHIFT 12
#define RISCV_PGSIZE (1 << RISCV_PGSHIFT)

#endif /* __riscv */

/**
 * \defgroup NMSIS_Core_CSR_Registers    Core CSR Registers
 * \ingroup  NMSIS_Core
 * \brief    NMSIS Core CSR Register Definitions
 * \details
 *
 * The following macros are used for CSR Register Defintions.
 *   @{
 */
/* === Standard RISC-V CSR Registers === */
#define CSR_USTATUS 0x0
#define CSR_FFLAGS 0x1
#define CSR_FRM 0x2
#define CSR_FCSR 0x3
#define CSR_VSTART 0x8
#define CSR_VXSAT 0x9
#define CSR_VXRM 0xa
#define CSR_VCSR 0xf
#define CSR_SEED 0x15
#define CSR_JVT 0x17
#define CSR_CYCLE 0xc00
#define CSR_TIME 0xc01
#define CSR_INSTRET 0xc02
#define CSR_HPMCOUNTER3 0xc03
#define CSR_HPMCOUNTER4 0xc04
#define CSR_HPMCOUNTER5 0xc05
#define CSR_HPMCOUNTER6 0xc06
#define CSR_HPMCOUNTER7 0xc07
#define CSR_HPMCOUNTER8 0xc08
#define CSR_HPMCOUNTER9 0xc09
#define CSR_HPMCOUNTER10 0xc0a
#define CSR_HPMCOUNTER11 0xc0b
#define CSR_HPMCOUNTER12 0xc0c
#define CSR_HPMCOUNTER13 0xc0d
#define CSR_HPMCOUNTER14 0xc0e
#define CSR_HPMCOUNTER15 0xc0f
#define CSR_HPMCOUNTER16 0xc10
#define CSR_HPMCOUNTER17 0xc11
#define CSR_HPMCOUNTER18 0xc12
#define CSR_HPMCOUNTER19 0xc13
#define CSR_HPMCOUNTER20 0xc14
#define CSR_HPMCOUNTER21 0xc15
#define CSR_HPMCOUNTER22 0xc16
#define CSR_HPMCOUNTER23 0xc17
#define CSR_HPMCOUNTER24 0xc18
#define CSR_HPMCOUNTER25 0xc19
#define CSR_HPMCOUNTER26 0xc1a
#define CSR_HPMCOUNTER27 0xc1b
#define CSR_HPMCOUNTER28 0xc1c
#define CSR_HPMCOUNTER29 0xc1d
#define CSR_HPMCOUNTER30 0xc1e
#define CSR_HPMCOUNTER31 0xc1f
#define CSR_VL 0xc20
#define CSR_VTYPE 0xc21
#define CSR_VLENB 0xc22
#define CSR_TIMEH 0xc81
#define CSR_SSTATUS 0x100
#define CSR_SEDELEG 0x102
#define CSR_SIDELEG 0x103
#define CSR_SIE 0x104
#define CSR_STVEC 0x105
#define CSR_STVT 0x107
#define CSR_SCOUNTEREN 0x106
#define CSR_SENVCFG 0x10a
#define CSR_SSTATEEN0 0x10c
#define CSR_SSTATEEN1 0x10d
#define CSR_SSTATEEN2 0x10e
#define CSR_SSTATEEN3 0x10f
#define CSR_SSCRATCH 0x140
#define CSR_SEPC 0x141
#define CSR_SCAUSE 0x142
#define CSR_STVAL 0x143
#define CSR_SIP 0x144
#define CSR_STIMECMP 0x14d
#define CSR_STIMECMPH 0x15d
#define CSR_SATP 0x180
#define CSR_SCONTEXT 0x5a8
#define CSR_VSSTATUS 0x200
#define CSR_VSIE 0x204
#define CSR_VSTVEC 0x205
#define CSR_VSSCRATCH 0x240
#define CSR_VSEPC 0x241
#define CSR_VSCAUSE 0x242
#define CSR_VSTVAL 0x243
#define CSR_VSIP 0x244
#define CSR_VSTIMECMP 0x24d
#define CSR_VSATP 0x280
#define CSR_HSTATUS 0x600
#define CSR_HEDELEG 0x602
#define CSR_HIDELEG 0x603
#define CSR_HIE 0x604
#define CSR_HTIMEDELTA 0x605
#define CSR_HCOUNTEREN 0x606
#define CSR_HGEIE 0x607
#define CSR_HENVCFG 0x60a
#define CSR_HSTATEEN0 0x60c
#define CSR_HSTATEEN1 0x60d
#define CSR_HSTATEEN2 0x60e
#define CSR_HSTATEEN3 0x60f
#define CSR_HTVAL 0x643
#define CSR_HIP 0x644
#define CSR_HVIP 0x645
#define CSR_HTINST 0x64a
#define CSR_HGATP 0x680
#define CSR_HCONTEXT 0x6a8
#define CSR_HGEIP 0xe12
#define CSR_SCOUNTOVF 0xda0
#define CSR_UTVT 0x7
#define CSR_UNXTI 0x45
#define CSR_UINTSTATUS 0x46
#define CSR_USCRATCHCSW 0x48
#define CSR_USCRATCHCSWL 0x49
#define CSR_STVT 0x107
#define CSR_SNXTI 0x145
#define CSR_SINTSTATUS 0x146
#define CSR_SSCRATCHCSW 0x148
#define CSR_SSCRATCHCSWL 0x149
#define CSR_MTVT 0x307
#define CSR_MNXTI 0x345
#define CSR_MINTSTATUS 0x346
#define CSR_MSCRATCHCSW 0x348
#define CSR_MSCRATCHCSWL 0x349
#define CSR_MSTATUS 0x300
#define CSR_MISA 0x301
#define CSR_MEDELEG 0x302
#define CSR_MIDELEG 0x303
#define CSR_MIE 0x304
#define CSR_MTVEC 0x305
#define CSR_MCOUNTEREN 0x306
#define CSR_MENVCFG 0x30a
#define CSR_MENVCFGH 0x31a
#define CSR_MSTATEEN0 0x30c
#define CSR_MSTATEEN1 0x30d
#define CSR_MSTATEEN2 0x30e
#define CSR_MSTATEEN3 0x30f
#define CSR_MCOUNTINHIBIT 0x320
#define CSR_MSCRATCH 0x340
#define CSR_MEPC 0x341
#define CSR_MCAUSE 0x342
#define CSR_MTVAL 0x343
#define CSR_MBADADDR 0x343
#define CSR_MIP 0x344
#define CSR_MTINST 0x34a
#define CSR_MTVAL2 0x34b
#define CSR_PMPCFG0 0x3a0
#define CSR_PMPCFG1 0x3a1
#define CSR_PMPCFG2 0x3a2
#define CSR_PMPCFG3 0x3a3
#define CSR_PMPCFG4 0x3a4
#define CSR_PMPCFG5 0x3a5
#define CSR_PMPCFG6 0x3a6
#define CSR_PMPCFG7 0x3a7
#define CSR_PMPCFG8 0x3a8
#define CSR_PMPCFG9 0x3a9
#define CSR_PMPCFG10 0x3aa
#define CSR_PMPCFG11 0x3ab
#define CSR_PMPCFG12 0x3ac
#define CSR_PMPCFG13 0x3ad
#define CSR_PMPCFG14 0x3ae
#define CSR_PMPCFG15 0x3af
#define CSR_PMPADDR0 0x3b0
#define CSR_PMPADDR1 0x3b1
#define CSR_PMPADDR2 0x3b2
#define CSR_PMPADDR3 0x3b3
#define CSR_PMPADDR4 0x3b4
#define CSR_PMPADDR5 0x3b5
#define CSR_PMPADDR6 0x3b6
#define CSR_PMPADDR7 0x3b7
#define CSR_PMPADDR8 0x3b8
#define CSR_PMPADDR9 0x3b9
#define CSR_PMPADDR10 0x3ba
#define CSR_PMPADDR11 0x3bb
#define CSR_PMPADDR12 0x3bc
#define CSR_PMPADDR13 0x3bd
#define CSR_PMPADDR14 0x3be
#define CSR_PMPADDR15 0x3bf
#define CSR_PMPADDR16 0x3c0
#define CSR_PMPADDR17 0x3c1
#define CSR_PMPADDR18 0x3c2
#define CSR_PMPADDR19 0x3c3
#define CSR_PMPADDR20 0x3c4
#define CSR_PMPADDR21 0x3c5
#define CSR_PMPADDR22 0x3c6
#define CSR_PMPADDR23 0x3c7
#define CSR_PMPADDR24 0x3c8
#define CSR_PMPADDR25 0x3c9
#define CSR_PMPADDR26 0x3ca
#define CSR_PMPADDR27 0x3cb
#define CSR_PMPADDR28 0x3cc
#define CSR_PMPADDR29 0x3cd
#define CSR_PMPADDR30 0x3ce
#define CSR_PMPADDR31 0x3cf
#define CSR_PMPADDR32 0x3d0
#define CSR_PMPADDR33 0x3d1
#define CSR_PMPADDR34 0x3d2
#define CSR_PMPADDR35 0x3d3
#define CSR_PMPADDR36 0x3d4
#define CSR_PMPADDR37 0x3d5
#define CSR_PMPADDR38 0x3d6
#define CSR_PMPADDR39 0x3d7
#define CSR_PMPADDR40 0x3d8
#define CSR_PMPADDR41 0x3d9
#define CSR_PMPADDR42 0x3da
#define CSR_PMPADDR43 0x3db
#define CSR_PMPADDR44 0x3dc
#define CSR_PMPADDR45 0x3dd
#define CSR_PMPADDR46 0x3de
#define CSR_PMPADDR47 0x3df
#define CSR_PMPADDR48 0x3e0
#define CSR_PMPADDR49 0x3e1
#define CSR_PMPADDR50 0x3e2
#define CSR_PMPADDR51 0x3e3
#define CSR_PMPADDR52 0x3e4
#define CSR_PMPADDR53 0x3e5
#define CSR_PMPADDR54 0x3e6
#define CSR_PMPADDR55 0x3e7
#define CSR_PMPADDR56 0x3e8
#define CSR_PMPADDR57 0x3e9
#define CSR_PMPADDR58 0x3ea
#define CSR_PMPADDR59 0x3eb
#define CSR_PMPADDR60 0x3ec
#define CSR_PMPADDR61 0x3ed
#define CSR_PMPADDR62 0x3ee
#define CSR_PMPADDR63 0x3ef
#define CSR_MSECCFG 0x747
#define CSR_TSELECT 0x7a0
#define CSR_TDATA1 0x7a1
#define CSR_TDATA2 0x7a2
#define CSR_TDATA3 0x7a3
#define CSR_TINFO 0x7a4
#define CSR_TCONTROL 0x7a5
#define CSR_MCONTEXT 0x7a8
#define CSR_MSCONTEXT 0x7aa
#define CSR_DCSR 0x7b0
#define CSR_DPC 0x7b1
#define CSR_DSCRATCH0 0x7b2
#define CSR_DSCRATCH1 0x7b3
#define CSR_MCYCLE 0xb00
#define CSR_MINSTRET 0xb02
#define CSR_MHPMCOUNTER3 0xb03
#define CSR_MHPMCOUNTER4 0xb04
#define CSR_MHPMCOUNTER5 0xb05
#define CSR_MHPMCOUNTER6 0xb06
#define CSR_MHPMCOUNTER7 0xb07
#define CSR_MHPMCOUNTER8 0xb08
#define CSR_MHPMCOUNTER9 0xb09
#define CSR_MHPMCOUNTER10 0xb0a
#define CSR_MHPMCOUNTER11 0xb0b
#define CSR_MHPMCOUNTER12 0xb0c
#define CSR_MHPMCOUNTER13 0xb0d
#define CSR_MHPMCOUNTER14 0xb0e
#define CSR_MHPMCOUNTER15 0xb0f
#define CSR_MHPMCOUNTER16 0xb10
#define CSR_MHPMCOUNTER17 0xb11
#define CSR_MHPMCOUNTER18 0xb12
#define CSR_MHPMCOUNTER19 0xb13
#define CSR_MHPMCOUNTER20 0xb14
#define CSR_MHPMCOUNTER21 0xb15
#define CSR_MHPMCOUNTER22 0xb16
#define CSR_MHPMCOUNTER23 0xb17
#define CSR_MHPMCOUNTER24 0xb18
#define CSR_MHPMCOUNTER25 0xb19
#define CSR_MHPMCOUNTER26 0xb1a
#define CSR_MHPMCOUNTER27 0xb1b
#define CSR_MHPMCOUNTER28 0xb1c
#define CSR_MHPMCOUNTER29 0xb1d
#define CSR_MHPMCOUNTER30 0xb1e
#define CSR_MHPMCOUNTER31 0xb1f
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324
#define CSR_MHPMEVENT5 0x325
#define CSR_MHPMEVENT6 0x326
#define CSR_MHPMEVENT7 0x327
#define CSR_MHPMEVENT8 0x328
#define CSR_MHPMEVENT9 0x329
#define CSR_MHPMEVENT10 0x32a
#define CSR_MHPMEVENT11 0x32b
#define CSR_MHPMEVENT12 0x32c
#define CSR_MHPMEVENT13 0x32d
#define CSR_MHPMEVENT14 0x32e
#define CSR_MHPMEVENT15 0x32f
#define CSR_MHPMEVENT16 0x330
#define CSR_MHPMEVENT17 0x331
#define CSR_MHPMEVENT18 0x332
#define CSR_MHPMEVENT19 0x333
#define CSR_MHPMEVENT20 0x334
#define CSR_MHPMEVENT21 0x335
#define CSR_MHPMEVENT22 0x336
#define CSR_MHPMEVENT23 0x337
#define CSR_MHPMEVENT24 0x338
#define CSR_MHPMEVENT25 0x339
#define CSR_MHPMEVENT26 0x33a
#define CSR_MHPMEVENT27 0x33b
#define CSR_MHPMEVENT28 0x33c
#define CSR_MHPMEVENT29 0x33d
#define CSR_MHPMEVENT30 0x33e
#define CSR_MHPMEVENT31 0x33f
#define CSR_MVENDORID 0xf11
#define CSR_MARCHID 0xf12
#define CSR_MIMPID 0xf13
#define CSR_MHARTID 0xf14
#define CSR_MCONFIGPTR 0xf15
#define CSR_STIMECMPH 0x15d
#define CSR_VSTIMECMPH 0x25d
#define CSR_HTIMEDELTAH 0x615
#define CSR_HENVCFGH 0x61a
#define CSR_HSTATEEN0H 0x61c
#define CSR_HSTATEEN1H 0x61d
#define CSR_HSTATEEN2H 0x61e
#define CSR_HSTATEEN3H 0x61f
#define CSR_CYCLEH 0xc80
#define CSR_TIMEH 0xc81
#define CSR_INSTRETH 0xc82
#define CSR_HPMCOUNTER3H 0xc83
#define CSR_HPMCOUNTER4H 0xc84
#define CSR_HPMCOUNTER5H 0xc85
#define CSR_HPMCOUNTER6H 0xc86
#define CSR_HPMCOUNTER7H 0xc87
#define CSR_HPMCOUNTER8H 0xc88
#define CSR_HPMCOUNTER9H 0xc89
#define CSR_HPMCOUNTER10H 0xc8a
#define CSR_HPMCOUNTER11H 0xc8b
#define CSR_HPMCOUNTER12H 0xc8c
#define CSR_HPMCOUNTER13H 0xc8d
#define CSR_HPMCOUNTER14H 0xc8e
#define CSR_HPMCOUNTER15H 0xc8f
#define CSR_HPMCOUNTER16H 0xc90
#define CSR_HPMCOUNTER17H 0xc91
#define CSR_HPMCOUNTER18H 0xc92
#define CSR_HPMCOUNTER19H 0xc93
#define CSR_HPMCOUNTER20H 0xc94
#define CSR_HPMCOUNTER21H 0xc95
#define CSR_HPMCOUNTER22H 0xc96
#define CSR_HPMCOUNTER23H 0xc97
#define CSR_HPMCOUNTER24H 0xc98
#define CSR_HPMCOUNTER25H 0xc99
#define CSR_HPMCOUNTER26H 0xc9a
#define CSR_HPMCOUNTER27H 0xc9b
#define CSR_HPMCOUNTER28H 0xc9c
#define CSR_HPMCOUNTER29H 0xc9d
#define CSR_HPMCOUNTER30H 0xc9e
#define CSR_HPMCOUNTER31H 0xc9f
#define CSR_MSTATUSH 0x310
#define CSR_MENVCFGH 0x31a
#define CSR_MSTATEEN0H 0x31c
#define CSR_MSTATEEN1H 0x31d
#define CSR_MSTATEEN2H 0x31e
#define CSR_MSTATEEN3H 0x31f
#define CSR_MHPMEVENT3H 0x723
#define CSR_MHPMEVENT4H 0x724
#define CSR_MHPMEVENT5H 0x725
#define CSR_MHPMEVENT6H 0x726
#define CSR_MHPMEVENT7H 0x727
#define CSR_MHPMEVENT8H 0x728
#define CSR_MHPMEVENT9H 0x729
#define CSR_MHPMEVENT10H 0x72a
#define CSR_MHPMEVENT11H 0x72b
#define CSR_MHPMEVENT12H 0x72c
#define CSR_MHPMEVENT13H 0x72d
#define CSR_MHPMEVENT14H 0x72e
#define CSR_MHPMEVENT15H 0x72f
#define CSR_MHPMEVENT16H 0x730
#define CSR_MHPMEVENT17H 0x731
#define CSR_MHPMEVENT18H 0x732
#define CSR_MHPMEVENT19H 0x733
#define CSR_MHPMEVENT20H 0x734
#define CSR_MHPMEVENT21H 0x735
#define CSR_MHPMEVENT22H 0x736
#define CSR_MHPMEVENT23H 0x737
#define CSR_MHPMEVENT24H 0x738
#define CSR_MHPMEVENT25H 0x739
#define CSR_MHPMEVENT26H 0x73a
#define CSR_MHPMEVENT27H 0x73b
#define CSR_MHPMEVENT28H 0x73c
#define CSR_MHPMEVENT29H 0x73d
#define CSR_MHPMEVENT30H 0x73e
#define CSR_MHPMEVENT31H 0x73f
#define CSR_MSECCFGH 0x757
#define CSR_MCYCLEH 0xb80
#define CSR_MINSTRETH 0xb82
#define CSR_MHPMCOUNTER3H 0xb83
#define CSR_MHPMCOUNTER4H 0xb84
#define CSR_MHPMCOUNTER5H 0xb85
#define CSR_MHPMCOUNTER6H 0xb86
#define CSR_MHPMCOUNTER7H 0xb87
#define CSR_MHPMCOUNTER8H 0xb88
#define CSR_MHPMCOUNTER9H 0xb89
#define CSR_MHPMCOUNTER10H 0xb8a
#define CSR_MHPMCOUNTER11H 0xb8b
#define CSR_MHPMCOUNTER12H 0xb8c
#define CSR_MHPMCOUNTER13H 0xb8d
#define CSR_MHPMCOUNTER14H 0xb8e
#define CSR_MHPMCOUNTER15H 0xb8f
#define CSR_MHPMCOUNTER16H 0xb90
#define CSR_MHPMCOUNTER17H 0xb91
#define CSR_MHPMCOUNTER18H 0xb92
#define CSR_MHPMCOUNTER19H 0xb93
#define CSR_MHPMCOUNTER20H 0xb94
#define CSR_MHPMCOUNTER21H 0xb95
#define CSR_MHPMCOUNTER22H 0xb96
#define CSR_MHPMCOUNTER23H 0xb97
#define CSR_MHPMCOUNTER24H 0xb98
#define CSR_MHPMCOUNTER25H 0xb99
#define CSR_MHPMCOUNTER26H 0xb9a
#define CSR_MHPMCOUNTER27H 0xb9b
#define CSR_MHPMCOUNTER28H 0xb9c
#define CSR_MHPMCOUNTER29H 0xb9d
#define CSR_MHPMCOUNTER30H 0xb9e
#define CSR_MHPMCOUNTER31H 0xb9f

/* === TEE CSR Registers === */
#define CSR_SPMPCFG0            0x1A0
#define CSR_SPMPCFG1            0x1A1
#define CSR_SPMPCFG2            0x1A2
#define CSR_SPMPCFG3            0x1A3
#define CSR_SPMPADDR0           0x1B0
#define CSR_SPMPADDR1           0x1B1
#define CSR_SPMPADDR2           0x1B2
#define CSR_SPMPADDR3           0x1B3
#define CSR_SPMPADDR4           0x1B4
#define CSR_SPMPADDR5           0x1B5
#define CSR_SPMPADDR6           0x1B6
#define CSR_SPMPADDR7           0x1B7
#define CSR_SPMPADDR8           0x1B8
#define CSR_SPMPADDR9           0x1B9
#define CSR_SPMPADDR10          0x1BA
#define CSR_SPMPADDR11          0x1BB
#define CSR_SPMPADDR12          0x1BC
#define CSR_SPMPADDR13          0x1BD
#define CSR_SPMPADDR14          0x1BE
#define CSR_SPMPADDR15          0x1BF

#define CSR_SMPUCFG0            0x1A0
#define CSR_SMPUCFG1            0x1A1
#define CSR_SMPUCFG2            0x1A2
#define CSR_SMPUCFG3            0x1A3
#define CSR_SMPUADDR0           0x1B0
#define CSR_SMPUADDR1           0x1B1
#define CSR_SMPUADDR2           0x1B2
#define CSR_SMPUADDR3           0x1B3
#define CSR_SMPUADDR4           0x1B4
#define CSR_SMPUADDR5           0x1B5
#define CSR_SMPUADDR6           0x1B6
#define CSR_SMPUADDR7           0x1B7
#define CSR_SMPUADDR8           0x1B8
#define CSR_SMPUADDR9           0x1B9
#define CSR_SMPUADDR10          0x1BA
#define CSR_SMPUADDR11          0x1BB
#define CSR_SMPUADDR12          0x1BC
#define CSR_SMPUADDR13          0x1BD
#define CSR_SMPUADDR14          0x1BE
#define CSR_SMPUADDR15          0x1BF

#define CSR_SMPUSWITCH0         0x170
#define CSR_SMPUSWITCH1         0x171

/* === CLIC CSR Registers === */
#define CSR_MTVT                0x307
#define CSR_MNXTI               0x345
#define CSR_MINTSTATUS          0x346
#define CSR_MSCRATCHCSW         0x348
#define CSR_MSCRATCHCSWL        0x349
#define CSR_MCLICBASE           0x350

/* === P-Extension Registers === */
#define CSR_UCODE               0x801

/* === Nuclei custom CSR Registers === */
//#define CSR_MCOUNTINHIBIT       0x320
#define CSR_MILM_CTL            0x7C0
#define CSR_MDLM_CTL            0x7C1
#define CSR_MECC_CODE           0x7C2
#define CSR_MNVEC               0x7C3
#define CSR_MSUBM               0x7C4
#define CSR_MDCAUSE             0x7C9
#define CSR_MCACHE_CTL          0x7CA
#define CSR_MMISC_CTL           0x7D0
#define CSR_MSAVESTATUS         0x7D6
#define CSR_MSAVEEPC1           0x7D7
#define CSR_MSAVECAUSE1         0x7D8
#define CSR_MSAVEEPC2           0x7D9
#define CSR_MSAVECAUSE2         0x7DA
#define CSR_MSAVEDCAUSE1        0x7DB
#define CSR_MSAVEDCAUSE2        0x7DC
#define CSR_MTLB_CTL            0x7DD
#define CSR_MECC_LOCK           0x7DE
#define CSR_MFP16MODE           0x7E2
/* mfp16mode is renamed to mmisc_ctl1 */
#define CSR_MMISC_CTL1          0x7E2
#define CSR_LSTEPFORC           0x7E9
#define CSR_PUSHMSUBM           0x7EB
#define CSR_MTVT2               0x7EC
#define CSR_JALMNXTI            0x7ED
#define CSR_PUSHMCAUSE          0x7EE
#define CSR_PUSHMEPC            0x7EF
#define CSR_MPPICFG_INFO        0x7F0
#define CSR_MFIOCFG_INFO        0x7F1

/* === NCDEV === */
#define CSR_MDEVB               0x7F3
#define CSR_MDEVM               0x7F4
#define CSR_MNOCB               0x7F5
#define CSR_MNOCM               0x7F6
#define CSR_MMACRO_DEV_EN       0xBC8
#define CSR_MMACRO_NOC_EN       0xBC9
#define CSR_MMACRO_CA_EN        0xBCA
#define CSR_MATTRI0_BASE        0x7F3
#define CSR_MATTRI0_MASK        0x7F4
#define CSR_MATTRI1_BASE        0x7F5
#define CSR_MATTRI1_MASK        0x7F6
#define CSR_MATTRI2_BASE        0x7F9
#define CSR_MATTRI2_MASK        0x7FA
#define CSR_MATTRI3_BASE        0x7FB
#define CSR_MATTRI3_MASK        0x7FC
#define CSR_MATTRI4_BASE        0x7FD
#define CSR_MATTRI4_MASK        0x7FE
#define CSR_MATTRI5_BASE        0xBE0
#define CSR_MATTRI5_MASK        0xBE1
#define CSR_MATTRI6_BASE        0xBE2
#define CSR_MATTRI6_MASK        0xBE3
#define CSR_MATTRI7_BASE        0xBE4
#define CSR_MATTRI7_MASK        0xBE5
#define CSR_SATTRI0_BASE        0x5F0
#define CSR_SATTRI0_MASK        0x5F1
#define CSR_SATTRI1_BASE        0x5F2
#define CSR_SATTRI1_MASK        0x5F3
#define CSR_SATTRI2_BASE        0x5F4
#define CSR_SATTRI2_MASK        0x5F5
#define CSR_SATTRI3_BASE        0x5F6
#define CSR_SATTRI3_MASK        0x5F7
#define CSR_SATTRI4_BASE        0x5F8
#define CSR_SATTRI4_MASK        0x5F9
#define CSR_SATTRI5_BASE        0x5FA
#define CSR_SATTRI5_MASK        0x5FB
#define CSR_SATTRI6_BASE        0x5FC
#define CSR_SATTRI6_MASK        0x5FD
#define CSR_SATTRI7_BASE        0x5FE
#define CSR_SATTRI7_MASK        0x5FF

/* === IREGION === */
#define CSR_MSMPCFG_INFO        0x7F7
#define CSR_MIRGB_INFO          0x7F7

#define CSR_SLEEPVALUE          0x811
#define CSR_TXEVT               0x812
#define CSR_WFE                 0x810
#define CSR_JALSNXTI            0x947
#define CSR_STVT2               0x948
#define CSR_PUSHSCAUSE          0x949
#define CSR_PUSHSEPC            0x94A
#define CSR_SDCAUSE             0x9C0
#define CSR_MICFG_INFO          0xFC0
#define CSR_MDCFG_INFO          0xFC1
#define CSR_MCFG_INFO           0xFC2
#define CSR_MTLBCFG_INFO        0xFC3

/* === ECC === */
#define CSR_MECC_CTL            0xBC0
#define CSR_MECC_STATUS         0xBC4

/* === STL === */
#define CSR_SAFETY_CRC_CTL      0x813
#define CSR_SAFETY_STL_STATUS   0x814

/* === Stack protect === */
#define CSR_MSTACK_CTRL         0x7C6
#define CSR_MSTACK_CTL          0x7C6
#define CSR_MSTACK_BOUND        0x7C7
#define CSR_MSTACK_BASE         0x7C8

/* === Nuclei CCM Registers === */
#define CSR_CCM_MBEGINADDR      0x7CB
#define CSR_CCM_MCOMMAND        0x7CC
#define CSR_CCM_MDATA           0x7CD
#define CSR_CCM_SUEN            0x7CE
#define CSR_CCM_SBEGINADDR      0x5CB
#define CSR_CCM_SCOMMAND        0x5CC
#define CSR_CCM_SDATA           0x5CD
#define CSR_CCM_UBEGINADDR      0x4CB
#define CSR_CCM_UCOMMAND        0x4CC
#define CSR_CCM_UDATA           0x4CD
#define CSR_CCM_FPIPE           0x4CF

#define CSR_SHARTID             0xDC0
/* === Worldguard CSRs === */
#define CSR_MLWID               0x390
#define CSR_MWIDDELEG           0x738
#define CSR_SLWID               0x190

/** @} */ /** End of Doxygen Group NMSIS_Core_CSR_Registers **/

/* Exception Code in MCAUSE CSR */
#define CAUSE_MISALIGNED_FETCH 0x0
#define CAUSE_FAULT_FETCH 0x1
#define CAUSE_ILLEGAL_INSTRUCTION 0x2
#define CAUSE_BREAKPOINT 0x3
#define CAUSE_MISALIGNED_LOAD 0x4
#define CAUSE_FAULT_LOAD 0x5
#define CAUSE_MISALIGNED_STORE 0x6
#define CAUSE_FAULT_STORE 0x7
#define CAUSE_USER_ECALL 0x8
#define CAUSE_SUPERVISOR_ECALL 0x9
#define CAUSE_HYPERVISOR_ECALL 0xa
#define CAUSE_MACHINE_ECALL 0xb
#define CAUSE_FETCH_PAGE_FAULT 0xc
#define CAUSE_LOAD_PAGE_FAULT 0xd
#define CAUSE_STORE_PAGE_FAULT 0xf

/* Delegatable Exception Code Mask in MCAUSE CSR*/
#define MISALIGNED_FETCH            (1 << CAUSE_MISALIGNED_FETCH)
#define FAULT_FETCH                 (1 << CAUSE_FAULT_FETCH)
#define ILLEGAL_INSTRUCTION         (1 << CAUSE_ILLEGAL_INSTRUCTION)
#define BREAKPOINT                  (1 << CAUSE_BREAKPOINT)
#define MISALIGNED_LOAD             (1 << CAUSE_MISALIGNED_LOAD)
#define FAULT_LOAD                  (1 << CAUSE_FAULT_LOAD)
#define MISALIGNED_STORE            (1 << CAUSE_MISALIGNED_STORE)
#define FAULT_STORE                 (1 << CAUSE_FAULT_STORE)
#define USER_ECALL                  (1 << CAUSE_USER_ECALL)
#define FETCH_PAGE_FAULT            (1 << CAUSE_FETCH_PAGE_FAULT)
#define LOAD_PAGE_FAULT             (1 << CAUSE_LOAD_PAGE_FAULT)
#define STORE_PAGE_FAULT            (1 << CAUSE_STORE_PAGE_FAULT)

/* Exception Subcode in MDCAUSE CSR */
#define DCAUSE_FAULT_FETCH_PMP      0x1
#define DCAUSE_FAULT_FETCH_INST     0x2

#define DCAUSE_FAULT_LOAD_PMP       0x1
#define DCAUSE_FAULT_LOAD_INST      0x2
#define DCAUSE_FAULT_LOAD_NICE      0x3

#define DCAUSE_FAULT_STORE_PMP      0x1
#define DCAUSE_FAULT_STORE_INST     0x2

#ifdef SMODE_RTOS
#define CSR_XSTATUS                 CSR_SSTATUS
#define CSR_XTVEC                   CSR_STVEC
#define CSR_XCOUNTEREN              CSR_SCOUNTEREN
#define CSR_XIE                     CSR_SIE
#define CSR_XIP                     CSR_SIP
#define CSR_XSCRATCH                CSR_SSCRATCH
#define CSR_XEPC                    CSR_SEPC
#define CSR_XCAUSE                  CSR_SCAUSE
#define CSR_XTVAL                   CSR_STVAL
#define CSR_XENVCFG                 CSR_SENVCFG
#define CSR_XTVT                    CSR_STVT
#define CSR_XTVT2                   CSR_STVT2
#define CSR_XSCRATCHCSWL            CSR_SSCRATCHCSWL
#define CSR_XSCRATCHCSW             CSR_SSCRATCHCSW
#define CSR_XDCAUSE                 CSR_SDCAUSE
#define CSR_JALXNXTI                CSR_JALSNXTI
#define CSR_XINTSTATUS              CSR_SINTSTATUS
#define CSR_XNXTI                   CSR_SNXTI
#define CSR_PUSHXEPC                CSR_PUSHSEPC
#define CSR_PUSHXCAUSE              CSR_PUSHSCAUSE
#define XRET                        sret
#define eclic_xsip_handler          eclic_ssip_handler
#define eclic_xtip_handler          eclic_stip_handler
#define XSTATUS_XIE                 SSTATUS_SIE
#define x_exc_entry                 exc_entry_s
#define x_irq_entry                 irq_entry_s
#else
#define CSR_XSTATUS                 CSR_MSTATUS
#define CSR_XTVEC                   CSR_MTVEC
#define CSR_XCOUNTEREN              CSR_MCOUNTEREN
#define CSR_XIE                     CSR_MIE
#define CSR_XIP                     CSR_MIP
#define CSR_XSCRATCH                CSR_MSCRATCH
#define CSR_XEPC                    CSR_MEPC
#define CSR_XCAUSE                  CSR_MCAUSE
#define CSR_XSUBM                   CSR_MSUBM
#define CSR_XTVAL                   CSR_MTVAL
#define CSR_XENVCFG                 CSR_MENVCFG
#define CSR_XTVT                    CSR_MTVT
#define CSR_XTVT2                   CSR_MTVT2
#define CSR_XSCRATCHCSWL            CSR_MSCRATCHCSWL
#define CSR_XSCRATCHCSW             CSR_MSCRATCHCSW
#define CSR_XDCAUSE                 CSR_MDCAUSE
#define CSR_JALXNXTI                CSR_JALMNXTI
#define CSR_XINTSTATUS              CSR_MINTSTATUS
#define CSR_XNXTI                   CSR_MNXTI
#define CSR_PUSHXEPC                CSR_PUSHMEPC
#define CSR_PUSHXCAUSE              CSR_PUSHMCAUSE
#define XRET                        mret
#define eclic_xsip_handler          eclic_msip_handler
#define eclic_xtip_handler          eclic_mtip_handler
#define XSTATUS_XIE                 MSTATUS_MIE
#define x_exc_entry                 exc_entry
#define x_irq_entry                 irq_entry
#endif

/** @} */ /** End of Doxygen Group NMSIS_Core_CSR_Encoding **/

#ifdef __cplusplus
}
#endif
#endif /* __RISCV_ENCODING_H__ */
