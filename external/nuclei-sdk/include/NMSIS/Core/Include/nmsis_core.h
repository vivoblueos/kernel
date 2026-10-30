/*
 * Copyright (c) 2009-2019 Arm Limited. All rights reserved.
 * -- Adaptable modifications made for Nuclei Processors. --
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
#include <stdint.h>

#ifdef __cplusplus
 extern "C" {
#endif

#include "nmsis_version.h"

/**
 * \ingroup NMSIS_Core_VersionControl
 * @{
 */
/* The following macro __NUCLEI_N_REV/__NUCLEI_NX_REV/
 * __NUCLEI_CPU_REV/__NUCLEI_CPU_SERIES definition in this file
 * is only used for doxygen documentation generation,
 * The <Device>.h is the real file to define it by vendor
 */
#if defined(__ONLY_FOR_DOXYGEN_DOCUMENT_GENERATION__)
/**
 * \brief Nuclei N class core revision number
 * \details
 * Reversion number format: [15:8] revision number, [7:0] patch number
 * \attention
 * Deprecated, this define is exclusive with \ref __NUCLEI_NX_REV
 */
#define __NUCLEI_N_REV                   (0x0309)
/**
 * \brief Nuclei NX class core revision number
 * \details
 * Reversion number format: [15:8] revision number, [7:0] patch number
 * \attention
 * Deprecated, this define is exclusive with \ref __NUCLEI_N_REV
 */
#define __NUCLEI_NX_REV                  (0x0207)
/**
 * \brief Nuclei CPU core revision number
 * \details
 * Nuclei RISC-V CPU Revision Number vX.Y.Z, eg. v3.10.1
 * \attention
 * This define is exclusive with \ref __NUCLEI_CPU_SERIES
 */
#define __NUCLEI_CPU_REV                 (0x030A01)
/**
 * \brief Nuclei CPU core series
 * \details
 * Nuclei RISC-V CPU Series Number, eg, 0x200, 0x300, 0x600, 0x900
 * for 200, 300, 600, 900 series.
 * \attention
 * This define is used together with \ref __NUCLEI_CPU_REV
 */
#define __NUCLEI_CPU_SERIES              (0x0200)
#endif /* __ONLY_FOR_DOXYGEN_DOCUMENT_GENERATION__ */
/** @} */ /* End of Group NMSIS_Core_VersionControl */

#include "nmsis_compiler.h"     /* NMSIS compiler specific defines */

/* === Include Nuclei Core Related Headers === */
/* Include core base feature header file */
#include "core_feature_base.h"

/* Include core fpu feature header file */
#include "core_feature_fpu.h"
/* Include core dsp feature header file */
#include "core_feature_dsp.h"
/* Include core vector feature header file */
#include "core_feature_vector.h"
/* Include core bitmanip feature header file */
#include "core_feature_bitmanip.h"
/* Include core pmp feature header file */
#include "core_feature_pmp.h"
/* Include core spmp feature header file */
 #include "core_feature_spmp.h"
/* Include core cache feature header file */
#include "core_feature_cache.h"
/* Include core cidu feature header file */
#include "core_feature_cidu.h"
/* Include core pma feature header file */
#include "core_feature_pma.h"
/* Include compatiable functions header file */
#include "core_compatiable.h"

#ifndef __NMSIS_GENERIC
/* Include core eclic feature header file */
#include "core_feature_eclic.h"
/* Include core plic feature header file */
#include "core_feature_plic.h"
/* Include core systimer feature header file */
#include "core_feature_timer.h"
#endif

#ifdef __cplusplus
}
#endif
