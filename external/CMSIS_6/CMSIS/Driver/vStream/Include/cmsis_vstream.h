/******************************************************************************
 * @file     cmsis_vstream.h
 * @brief    CMSIS Virtual Streaming interface Driver definitions
 * @version  V1.0.0
 * @date     2. April 2025
 ******************************************************************************/
/*
 * Copyright (c) 2025 Arm Limited. All rights reserved.
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

#ifndef CMSIS_VSTREAM_H_
#define CMSIS_VSTREAM_H_

#ifdef  __cplusplus
extern  "C"
{
#endif

#include <stdint.h>

// Virtual Streaming Mode Codes
#define VSTREAM_MODE_CONTINUOUS         (0UL)       ///< Continuous mode (default)
#define VSTREAM_MODE_SINGLE             (1UL)       ///< Single-shot mode

// Virtual Streaming Event Flags
#define VSTREAM_EVENT_DATA              (1UL)       ///< Data block received/sent
#define VSTREAM_EVENT_OVERFLOW          (1UL << 1)  ///< Data buffer overflow
#define VSTREAM_EVENT_UNDERFLOW         (1UL << 2)  ///< Data buffer underflow
#define VSTREAM_EVENT_EOS               (1UL << 3)  ///< End of stream

// Virtual Streaming Return Codes
#define VSTREAM_OK                      (0)         ///< Operation succeeded
#define VSTREAM_ERROR                   (-1)        ///< Unspecified error
#define VSTREAM_ERROR_PARAMETER         (-2)        ///< Parameter error

// Virtual Streaming Status
typedef struct {
  uint32_t active       :  1;           ///< Streaming active
  uint32_t overflow     :  1;           ///< Data buffer overflow  (cleared on GetStatus)
  uint32_t underflow    :  1;           ///< Data buffer underflow (cleared on GetStatus)
  uint32_t eos          :  1;           ///< End Of Stream         (cleared on GetStatus)
  uint32_t reserved     : 28;
} vStreamStatus_t;

/**
  \fn           int32_t vStreamInitialize (vStreamEvent_t event_cb)
  \brief        Initialize Virtual Streaming interface.
  \return       \ref VSTREAM_OK on success; otherwise, an appropriate error code (see \ref vstream_return_code)

  \fn           int32_t vStreamUninitialize (void)
  \brief        De-initialize Virtual Streaming interface.
  \return       \ref VSTREAM_OK on success; otherwise, an \ref VSTREAM_ERROR error code (see \ref vstream_return_code)

  \fn           int32_t vStreamSetBuf (void *buf, uint32_t buf_size, uint32_t block_size)
  \brief        Set Virtual Streaming data buffer.
  \param[in]    buf             pointer to memory buffer used for streaming data
  \param[in]    buf_size        total size of the streaming data buffer (in bytes)
  \param[in]    block_size      streaming data block size (in bytes)
  \return       \ref VSTREAM_OK on success; otherwise, an appropriate error code (see \ref vstream_return_code)

  \fn           int32_t vStreamStart (uint32_t mode)
  \brief        Start streaming.
  \param[in]    mode            streaming mode (see \ref vstream_mode)
  \return       \ref VSTREAM_OK on success; otherwise, an appropriate error code (see \ref vstream_return_code)

  \fn           int32_t vStreamStop (void)
  \brief        Stop streaming.
  \return       \ref VSTREAM_OK on success; otherwise, an \ref VSTREAM_ERROR error code (see \ref vstream_return_code)

  \fn           void *vStreamGetBlock (void)
  \brief        Get pointer to Virtual Streaming data block.
  \return       pointer to data block, returns NULL if no block is available

  \fn           int32_t vStreamReleaseBlock (void)
  \brief        Release Virtual Streaming data block.
  \return       \ref VSTREAM_OK on success; otherwise, an \ref VSTREAM_ERROR error code (see \ref vstream_return_code)

  \fn           vStreamStatus_t vStreamGetStatus (void)
  \brief        Get Virtual Streaming status.
  \return       streaming status structure (see \ref vStreamStatus_t)

  \fn           void vStreamEvent (uint32_t event_flags)
  \brief        Callback function for handling Virtual Streaming events.
  \param[in]    event_flags     bitmask indicating one or more streaming events (see \ref vstream_events)
*/

typedef void (*vStreamEvent_t) (uint32_t event_flags);  ///< Pointer to \ref vStreamEvent : Handling of Virtual Streaming Events.


/**
\brief Access structure of the Virtual Streaming interface Driver.
*/
typedef struct vStreamDriver_s {
  int32_t         (*Initialize)   (vStreamEvent_t event_cb);                              ///< Pointer to \ref vStreamInitialize : Initialize Virtual Streaming interface.
  int32_t         (*Uninitialize) (void);                                                 ///< Pointer to \ref vStreamUninitialize : De-initialize Virtual Streaming interface.
  int32_t         (*SetBuf)       (void *buf, uint32_t buf_size, uint32_t block_size);    ///< Pointer to \ref vStreamSetBuf : Set Virtual Streaming data buffer.
  int32_t         (*Start)        (uint32_t mode);                                        ///< Pointer to \ref vStreamStart : Start streaming.
  int32_t         (*Stop)         (void);                                                 ///< Pointer to \ref vStreamStop : Stop streaming.
  void *          (*GetBlock)     (void);                                                 ///< Pointer to \ref vStreamGetBlock : Get pointer to data block.
  int32_t         (*ReleaseBlock) (void);                                                 ///< Pointer to \ref vStreamReleaseBlock : Release data block.
  vStreamStatus_t (*GetStatus)    (void);                                                 ///< Pointer to \ref vStreamGetStatus : Get Virtual Streaming status.
} const vStreamDriver_t;

#ifdef  __cplusplus
}
#endif

#endif  /* CMSIS_VSTREAM_H_ */
