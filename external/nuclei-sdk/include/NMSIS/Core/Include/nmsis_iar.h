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

#ifndef __NMSIS_IAR_H__
#define __NMSIS_IAR_H__
/*!
 * @file     nmsis_iar.h
 * @brief    NMSIS compiler IAR header file
 */
#include <stdint.h>

#ifdef __cplusplus
 extern "C" {
#endif

#include "riscv_encoding.h"

/* #########################  Startup and Lowlevel Init  ######################## */
/**
 * \defgroup NMSIS_Core_CompilerControl    Compiler Control
 * \ingroup  NMSIS_Core
 * \brief    Compiler agnostic \#define symbols for generic c/c++ source code
 * \details
 *
 * The NMSIS-Core provides the header file <b>nmsis_compiler.h</b> with consistent \#define symbols for generate C or C++ source files that should be compiler agnostic.
 * Each NMSIS compliant compiler should support the functionality described in this section.
 *
 * The header file <b>nmsis_compiler.h</b> is also included by each Device Header File <device.h> so that these definitions are available.
 *   @{
 */

/* Fallback for __has_builtin */
#ifndef __has_builtin
  #define __has_builtin(x) (0)
#endif

/* NMSIS compiler specific defines */
/** \brief Pass information from the compiler to the assembler. */
#ifndef   __ASM
  #define __ASM                                  __asm
#endif

/** \brief Recommend that function should be inlined by the compiler. */
#ifndef   __INLINE
  #define __INLINE                               inline
#endif

/** \brief Define a static function that may be inlined by the compiler. */
#ifndef   __STATIC_INLINE
  #define __STATIC_INLINE                        static inline
#endif

/** \brief Define a static function that should be always inlined by the compiler. */
#ifndef   __STATIC_FORCEINLINE
  #define __STATIC_FORCEINLINE                   __attribute__((always_inline)) static inline
#endif

/** \brief Inform the compiler that a function does not return. */
#ifndef   __NO_RETURN
  #define __NO_RETURN                            __attribute__((__noreturn__))
#endif

/** \brief Inform that a variable shall be retained in executable image. */
#ifndef   __USED
  #define __USED                                 __attribute__((used))
#endif

/** \brief restrict pointer qualifier to enable additional optimizations. */
#ifndef   __WEAK
  #define __WEAK                                 __attribute__((weak))
#endif

/** \brief specified the vector size of the variable, measured in bytes, not supported in IAR */
#ifndef   __VECTOR_SIZE
  #define __VECTOR_SIZE(x)
#endif

/** \brief Request smallest possible alignment. */
#ifndef   __PACKED
  #define __PACKED                               __attribute__((packed, aligned(1)))
#endif

/** \brief Request smallest possible alignment for a structure. */
#ifndef   __PACKED_STRUCT
  #define __PACKED_STRUCT                        struct __attribute__((packed, aligned(1)))
#endif

/** \brief Request smallest possible alignment for a union. */
#ifndef   __PACKED_UNION
  #define __PACKED_UNION                         union __attribute__((packed, aligned(1)))
#endif

#ifndef   __UNALIGNED_UINT16_WRITE
  #pragma language=save
  #pragma language=extended
  /** \brief Packed struct for unaligned uint16_t write access */
  __PACKED_STRUCT T_UINT16_WRITE {
      uint16_t v;
  };
  #pragma language=restore
  /** \brief Pointer for unaligned write of a uint16_t variable. */
  #define __UNALIGNED_UINT16_WRITE(addr, val)    (void)((((struct T_UINT16_WRITE *)(void *)(addr))->v) = (val))
#endif

#ifndef   __UNALIGNED_UINT16_READ
  #pragma language=save
  #pragma language=extended
  /** \brief Packed struct for unaligned uint16_t read access */
  __PACKED_STRUCT T_UINT16_READ {
      uint16_t v;
  };
  #pragma language=restore
  /** \brief Pointer for unaligned read of a uint16_t variable. */
  #define __UNALIGNED_UINT16_READ(addr)          (((const struct T_UINT16_READ *)(const void *)(addr))->v)
#endif

#ifndef   __UNALIGNED_UINT32_WRITE
  #pragma language=save
  #pragma language=extended
  /** \brief Packed struct for unaligned uint32_t write access */
  __PACKED_STRUCT T_UINT32_WRITE {
      uint32_t v;
  };
  #pragma language=restore
  /** \brief Pointer for unaligned write of a uint32_t variable. */
  #define __UNALIGNED_UINT32_WRITE(addr, val)    (void)((((struct T_UINT32_WRITE *)(void *)(addr))->v) = (val))
#endif

#ifndef   __UNALIGNED_UINT32_READ
  #pragma language=save
  #pragma language=extended
  /** \brief Packed struct for unaligned uint32_t read access */
  __PACKED_STRUCT T_UINT32_READ {
      uint32_t v;
  };
  #pragma language=restore
  /** \brief Pointer for unaligned read of a uint32_t variable. */
  #define __UNALIGNED_UINT32_READ(addr)          (((const struct T_UINT32_READ *)(const void *)(addr))->v)
#endif

/** \brief Minimum `x` bytes alignment for a variable. */
#ifndef   __ALIGNED
  #define __ALIGNED(x)                           __attribute__((aligned(x)))
#endif

/** \brief restrict pointer qualifier to enable additional optimizations. */
#ifndef   __RESTRICT
  #define __RESTRICT                             __restrict
#endif

/** \brief Barrier to prevent compiler from reordering instructions. */
#ifndef   __COMPILER_BARRIER
  #define __COMPILER_BARRIER()                   __ASM volatile("":::"memory")
#endif

/** \brief provide the compiler with branch prediction information, the branch is usually true */
#ifndef   __USUALLY
  #define __USUALLY(exp)                         (exp)
#endif

/** \brief provide the compiler with branch prediction information, the branch is rarely true */
#ifndef   __RARELY
  #define __RARELY(exp)                          (exp)
#endif

/** \brief Use this attribute to indicate that the specified function is an interrupt handler run in Machine Mode. */
#ifndef   __INTERRUPT
  #define __INTERRUPT                            __machine __interrupt
#endif

/** \brief Use this attribute to indicate that the specified function is an interrupt handler run in Machine Mode. */
#ifndef   __MACHINE_INTERRUPT
  #define __MACHINE_INTERRUPT                    __machine __interrupt
#endif

/** \brief Use this attribute to indicate that the specified function is an interrupt handler run in Supervisor Mode. */
#ifndef   __SUPERVISOR_INTERRUPT
  #define __SUPERVISOR_INTERRUPT                 __supervisor __interrupt
#endif

/** \brief Use this attribute to indicate that the specified function is an interrupt handler run in User Mode. */
#ifndef   __USER_INTERRUPT
  #define __USER_INTERRUPT                       __user __interrupt
#endif

/** @} */ /* End of Doxygen Group NMSIS_Core_CompilerControl */

#ifdef __cplusplus
}
#endif
#endif /* __NMSIS_GCC_H__ */
