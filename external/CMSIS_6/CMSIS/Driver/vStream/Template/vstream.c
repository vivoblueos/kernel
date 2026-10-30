/******************************************************************************
 * @file     vstream.c
 * @brief    CMSIS Virtual Streaming interface Driver implementation template
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

#include <stddef.h>
#include "cmsis_vstream.h"

#include "RTE_Components.h"
#include CMSIS_device_header

// Add user includes here:


// Variables

static vStreamEvent_t fn_event_cb;      // Event handling callback function

// Add user types and variables here:


// Functions

// Add user functions here:

/**
  \fn           int32_t Initialize (vStreamEvent_t event_cb)
  \brief        Initialize Virtual Streaming interface.
  \return       VSTREAM_OK on success; otherwise, an appropriate error code
*/
static int32_t Initialize (vStreamEvent_t event_cb) {

  // Register event callback function
  fn_event_cb = event_cb;

  // Add user code here:

  return VSTREAM_OK;
}

/**
  \fn           int32_t Uninitialize (void)
  \brief        De-initialize Virtual Streaming interface.
  \return       VSTREAM_OK on success; otherwise, an VSTREAM_ERROR error code
*/
static int32_t Uninitialize (void) {

  // De-register event callback function
  fn_event_cb = NULL;

  // Add user code here:

  return VSTREAM_OK;
}

/**
  \fn           int32_t SetBuf (void *buf, uint32_t buf_size, uint32_t block_size)
  \brief        Set Virtual Streaming data buffer.
  \param[in]    buf             pointer to memory buffer used for streaming data
  \param[in]    buf_size        total size of the streaming data buffer (in bytes)
  \param[in]    block_size      streaming data block size (in bytes)
  \return       VSTREAM_OK on success; otherwise, an appropriate error code
*/
static int32_t SetBuf (void *buf, uint32_t buf_size, uint32_t block_size) {
  (void)buf;
  (void)buf_size;
  (void)block_size;

  // Add user code here:

  return VSTREAM_OK;
}

/**
  \fn           int32_t Start (uint32_t mode)
  \brief        Start streaming.
  \param[in]    mode            streaming mode
  \return       VSTREAM_OK on success; otherwise, an appropriate error code
*/
static int32_t Start (uint32_t mode) {

  // Check parameters
  if ((mode != VSTREAM_MODE_CONTINUOUS) && (mode != VSTREAM_MODE_SINGLE)) {
    return VSTREAM_ERROR_PARAMETER;
  }

  // Add user code here:

  return VSTREAM_OK;
}

/**
  \fn           int32_t Stop (void)
  \brief        Stop streaming.
  \return       VSTREAM_OK on success; otherwise, an VSTREAM_ERROR error code
*/
static int32_t Stop (void) {

  // Add user code here:

  return VSTREAM_OK;
}

/**
  \fn           void *GetBlock (void)
  \brief        Get pointer to Virtual Streaming data block.
  \return       pointer to data block, returns NULL if no block is available
*/
static void *GetBlock (void) {

  // Add user code here:

  return NULL;
}

/**
  \fn           int32_t ReleaseBlock (void)
  \brief        Release Virtual Streaming data block.
  \return       VSTREAM_OK on success; otherwise, an VSTREAM_ERROR error code
*/
static int32_t ReleaseBlock (void) {
  return VSTREAM_OK;
}

/**
  \fn           vStreamStatus_t GetStatus (void)
  \brief        Get Virtual Streaming status.
  \return       streaming status structure
*/
static vStreamStatus_t GetStatus (void) {
  vStreamStatus_t stat = { 0U, 0U, 0U, 0U, 0U };

  // Add user code here:

  return stat;
}


// Driver structure

extern \
vStreamDriver_t Driver_vStreamDevice;
vStreamDriver_t Driver_vStreamDevice = {
  Initialize,
  Uninitialize,
  SetBuf,
  Start,
  Stop,
  GetBlock,
  ReleaseBlock,
  GetStatus
};
