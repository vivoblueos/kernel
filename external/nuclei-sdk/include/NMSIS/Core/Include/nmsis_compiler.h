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

#ifndef __NMSIS_COMPILER_H
#define __NMSIS_COMPILER_H

#include <stdint.h>

/*!
 * @file     nmsis_compiler.h
 * @brief    NMSIS compiler generic header file
 */
#if defined ( __GNUC__ )
  /* GNU GCC Compiler */
  #include "nmsis_gcc.h"
#elif defined ( __ICCRISCV__ )
  /* IAR Compiler */
  #include "nmsis_iar.h"
#else
  #error Unknown compiler.
#endif

/* IO definitions (access restrictions to peripheral registers) */
/**
 * \defgroup NMSIS_Core_PeriphAccess     Peripheral Access
 * \brief  Naming conventions and optional features for accessing peripherals.
 *
 * The section below describes the naming conventions, requirements, and optional features
 * for accessing device specific peripherals.
 * Most of the rules also apply to the core peripherals.
 *
 * The **Device Header File <device.h>** contains typically these definition
 * and also includes the core specific header files.
 *
 * @{
 */
/** \brief Defines 'read only' permissions */
#ifdef __cplusplus
  #define   __I     volatile
#else
  #define   __I     volatile const
#endif
/** \brief Defines 'write only' permissions */
#define     __O     volatile
/** \brief Defines 'read / write' permissions */
#define     __IO    volatile

/* following defines should be used for structure members */
/** \brief Defines 'read only' structure member permissions */
#define     __IM     volatile const
/** \brief Defines 'write only' structure member permissions */
#define     __OM     volatile
/** \brief Defines 'read/write' structure member permissions */
#define     __IOM    volatile

/**
 * \brief   Mask and shift a bit field value for use in a register bit range.
 * \details The macro \ref _VAL2FLD uses the #define's _Pos and _Msk of the related bit
 * field to shift bit-field values for assigning to a register.
 *
 * **Example**:
 * \code
 * ECLIC->CFG = _VAL2FLD(CLIC_CLICCFG_NLBIT, 3);
 * \endcode
 * \param[in] field  Name of the register bit field.
 * \param[in] value  Value of the bit field. This parameter is interpreted as an uint32_t type.
 * \return           Masked and shifted value.
 */
#define _VAL2FLD(field, value)    (((uint32_t)(value) << field ## _Pos) & field ## _Msk)

/**
 * \brief   Mask and shift a register value to extract a bit filed value.
 * \details The macro \ref _FLD2VAL uses the #define's _Pos and _Msk of the related bit
 * field to extract the value of a bit field from a register.
 *
 * **Example**:
 * \code
 * nlbits = _FLD2VAL(CLIC_CLICCFG_NLBIT, ECLIC->CFG);
 * \endcode
 * \param[in] field  Name of the register bit field.
 * \param[in] value  Value of register. This parameter is interpreted as an uint32_t type.
 * \return           Masked and shifted bit field value.
 */
#define _FLD2VAL(field, value)    (((uint32_t)(value) & field ## _Msk) >> field ## _Pos)

/** @} */ /* end of group NMSIS_Core_PeriphAccess */


#endif /* __NMSIS_COMPILER_H */

