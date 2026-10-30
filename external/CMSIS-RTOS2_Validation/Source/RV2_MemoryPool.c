/*
 * Copyright (C) 2022 ARM Limited or its affiliates. All rights reserved.
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

#include <string.h>
#include "cmsis_rv2.h"

/*-----------------------------------------------------------------------------
 *      Test implementation
 *----------------------------------------------------------------------------*/
#define MAX_MEMPOOL_NUM  64

#define MEMBL_CNT  4
#define MEMBL_SZ  32

/* Definitions for TC_MemPoolAllocAndFreeComb */
uint32_t LFSR_32Bit (void);

void Irq_osMemoryPoolNew_1          (void);
void Irq_osMemoryPoolGetName_1      (void);
void Irq_osMemoryPoolAlloc_1        (void);
void Irq_osMemoryPoolFree_1         (void);
void Irq_osMemoryPoolGetCapacity_1  (void);
void Irq_osMemoryPoolGetBlockSize_1 (void);
void Irq_osMemoryPoolGetCount_1     (void);
void Irq_osMemoryPoolGetSpace_1     (void);
void Irq_osMemoryPoolDelete_1       (void);

/*-----------------------------------------------------------------------------
 * 32-bit LFSR with maximal period (x^32 + x^31 + x^29 + x + 1)
 *----------------------------------------------------------------------------*/
uint32_t LFSR_32Bit (void) {
  static uint32_t lfsr = 0xAA55AA55;
  lfsr = (lfsr >> 1) ^ (-(lfsr & 1U) & 0xD0000001U);
  return (lfsr);
}

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup mempool_func Memory Pool Functions
\brief Memory Pool Functions Test Cases
\details
The test cases check the osPool* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolNew_1
\details
  - Call osMemoryPoolNew to create a memory pool object
  - Call osMemoryPoolNew from ISR
*/
void TC_osMemoryPoolNew_1 (void) {
#if (TC_OSMEMORYPOOLNEW_1_EN)
  osMemoryPoolId_t id;

  /* Call osMemoryPoolNew to create a memory pool object */
  id = osMemoryPoolNew (1U, 4U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created memory pool */
  ASSERT_TRUE (osMemoryPoolDelete(id) == osOK);

  /* Call osMemoryPoolNew from ISR */
  TST_IRQHandler = Irq_osMemoryPoolNew_1;
  MemoryPoolId = (osMemoryPoolId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (MemoryPoolId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLNEW_1_EN)
void Irq_osMemoryPoolNew_1 (void) {
  MemoryPoolId = osMemoryPoolNew (1U, 4U, NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolNew_2
\details
  - Call osMemoryPoolNew to create memory pool object and assign a name to it
*/
void TC_osMemoryPoolNew_2 (void) {
#if (TC_OSMEMORYPOOLNEW_2_EN)
  osMemoryPoolAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMemoryPoolId_t id;

  /* Call osMemoryPoolNew to create memory pool object and assign a name to it */
  attr.name = "MemoryPool";

  id = osMemoryPoolNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created memory pool */
  ASSERT_TRUE (osMemoryPoolDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolNew_3
\details
  - Call osMemoryPoolNew to create memory pool object by specifying memory for control block and data in attributes
*/
void TC_osMemoryPoolNew_3 (void) {
#if (TC_OSMEMORYPOOLNEW_3_EN)
  osMemoryPoolAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMemoryPoolId_t id;

  /* Call osMemoryPoolNew to create memory pool object by specifying memory for control block and data in attributes */
  attr.cb_mem  = &MemoryPool_CbMem;
  attr.cb_size = sizeof(MemoryPool_CbMem);
  attr.mp_mem  = &MemoryPool_DataMem;
  attr.mp_size = sizeof(MemoryPool_DataMem);

  id = osMemoryPoolNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created memory pool */
  ASSERT_TRUE (osMemoryPoolDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolGetName_1
\details
  - Call osMemoryPoolGetName to retrieve a name of an unnamed memory pool
  - Call osMemoryPoolGetName to retrieve a name of a memory pool with assigned name
  - Call osMemoryPoolGetName from ISR
  - Call osMemoryPoolGetName with null object
*/
void TC_osMemoryPoolGetName_1 (void) {
#if (TC_OSMEMORYPOOLGETNAME_1_EN)
  osMemoryPoolAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMemoryPoolId_t id;
  char const *name = "MemoryPool";

  /* Create memory pool object without assigned name */
  attr.name = NULL;
  id = osMemoryPoolNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMemoryPoolGetName to retrieve a name of an unnamed memory pool */
  ASSERT_TRUE(osMemoryPoolGetName (id) == NULL);

  /* Delete memory pool object */
  osMemoryPoolDelete (id);


  /* Create memory pool object with name assigned via attributes */
  attr.name = name;
  id = osMemoryPoolNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMemoryPoolGetName to retrieve a name of a memory pool with assigned name */
  ASSERT_TRUE (strcmp(osMemoryPoolGetName(id), name) == 0U);

  /* Call osMemoryPoolGetName from ISR */
  TST_IRQHandler = Irq_osMemoryPoolGetName_1;
  MemoryPoolId   = id;
  MemoryPoolName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(MemoryPoolName, name) == 0U);

  /* Delete memory pool object */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolGetName with null object */
  ASSERT_TRUE (osMemoryPoolGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLGETNAME_1_EN)
void Irq_osMemoryPoolGetName_1 (void) {
  MemoryPoolName = osMemoryPoolGetName (MemoryPoolId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolAlloc_1
\details
  - Call osMemoryPoolAlloc to allocate a memory block from the memory pool
  - Call osMemoryPoolAlloc from ISR with timeout == 0
  - Call osMemoryPoolAlloc from ISR with timeout != 0
  - Call osMemoryPoolAlloc with null object
*/
void TC_osMemoryPoolAlloc_1 (void) {
#if (TC_OSMEMORYPOOLALLOC_1_EN)
  osMemoryPoolId_t id;
  void *p;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMemoryPoolAlloc to allocate a memory block from the memory pool */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Delete memory pool */
  osMemoryPoolDelete (id);


  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMemoryPoolAlloc from ISR */
  TST_IRQHandler = Irq_osMemoryPoolAlloc_1;
  MemoryPoolId = id;

  /* Call osMemoryPoolAlloc from ISR with timeout == 0 */
  Isr_s32 = 0;
  Isr_pv  = NULL;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_pv != NULL);

  /* Call osMemoryPoolAlloc from ISR with timeout != 0 */
  Isr_s32 = 1;
  Isr_pv  = (void *)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_pv == NULL);

  /* Delete memory pool */
  osMemoryPoolDelete (id);


  /* Call osMemoryPoolAlloc with null object */
  ASSERT_TRUE (osMemoryPoolAlloc (NULL, 0U) == NULL);

  /* Call osMemoryPoolAlloc from ISR with null object */
  Isr_s32 = 2;
  Isr_pv  = (void *)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_pv == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolAlloc_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLALLOC_1_EN)
void Irq_osMemoryPoolAlloc_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMemoryPoolAlloc from ISR with timeout == 0 */
      Isr_pv = osMemoryPoolAlloc (MemoryPoolId, 0U);
      break;

    case 1:
      /* Call osMemoryPoolAlloc from ISR with timeout != 0 */
      Isr_pv = osMemoryPoolAlloc (MemoryPoolId, osWaitForever);
      break;

    case 2:
      /* Call osMemoryPoolAlloc from ISR with null object */
      Isr_pv = osMemoryPoolAlloc (NULL, 0U);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolFree_1
\details
  - Call osMemoryPoolFree to free a memory block from the memory pool
  - Call osMemoryPoolFree from ISR
  - Call osMemoryPoolFree with null object
  - Call osMemoryPoolFree from ISR with null object
  - Call osMemoryPoolFree from ISR with null block pointer
*/
void TC_osMemoryPoolFree_1 (void) {
#if (TC_OSMEMORYPOOLFREE_1_EN)
  osMemoryPoolId_t id;
  void *p;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Allocate one block */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Call osMemoryPoolFree to free a memory block from the memory pool */
  ASSERT_TRUE (osMemoryPoolFree (id, p) == osOK);

  /* Allocate one block */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Call osMemoryPoolFree from ISR */
  TST_IRQHandler = Irq_osMemoryPoolFree_1;
  MemoryPoolId = id;
  Isr_u32 = 0U;
  Isr_pv  = p;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osOK);

  /* Allocate one block */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Call osMemoryPoolFree with null object */
  ASSERT_TRUE (osMemoryPoolFree (NULL, p) == osErrorParameter);

  /* Call osMemoryPoolFree from ISR with null object */
  Isr_u32 = 1U;
  Isr_pv  = p;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);

  /* Call osMemoryPoolFree from ISR with null block pointer */
  Isr_u32 = 2U;
  Isr_pv  = NULL;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);

  /* Delete memory pool */
  osMemoryPoolDelete (id);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolFree_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLFREE_1_EN)
void Irq_osMemoryPoolFree_1 (void) {
  void *block;

  block = (void *)(uint32_t)Isr_pv;

  switch (Isr_u32) {
    case 0:
      /* Call osMemoryPoolFree from ISR */
      Isr_osStatus = osMemoryPoolFree (MemoryPoolId, block);
      break;

    case 1:
      /* Call osMemoryPoolFree from ISR with null object */
      Isr_osStatus = osMemoryPoolFree (NULL, block);
      break;

    case 2:
      /* Call osMemoryPoolFree from ISR with null block pointer */
      Isr_osStatus = osMemoryPoolFree (MemoryPoolId, NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolGetCapacity_1
\details
  - Call osMemoryPoolGetCapacity to retrieve the maximum number of available memory blocks
  - Call osMemoryPoolGetCapacity from ISR
  - Call osMemoryPoolGetCapacity from ISR with null object
  - Call osMemoryPoolGetCapacity with null object
*/
void TC_osMemoryPoolGetCapacity_1 (void) {
#if (TC_OSMEMORYPOOLGETCAPACITY_1_EN)
  osMemoryPoolId_t id;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMemoryPoolGetCapacity to retrieve the maximum number of available memory blocks */
  ASSERT_TRUE (osMemoryPoolGetCapacity (id) == MEMBL_CNT);

  /* Call osMemoryPoolGetCapacity from ISR */
  TST_IRQHandler = Irq_osMemoryPoolGetCapacity_1;
  MemoryPoolId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == MEMBL_CNT);

  /* Call osMemoryPoolGetCapacity from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MEMBL_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete memory pool */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolGetCapacity with null object */
  ASSERT_TRUE (osMemoryPoolGetCapacity (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolGetCapacity_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLGETCAPACITY_1_EN)
void Irq_osMemoryPoolGetCapacity_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMemoryPoolGetCapacity from ISR */
      Isr_u32 = osMemoryPoolGetCapacity (MemoryPoolId);
      break;

    case 1:
      /* Call osMemoryPoolGetCapacity from ISR with null object */
      Isr_u32 = osMemoryPoolGetCapacity (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolGetBlockSize_1
\details
  - Call osMemoryPoolGetBlockSize to retrieve the memory block size
  - Call osMemoryPoolGetBlockSize from ISR
  - Call osMemoryPoolGetBlockSize from ISR with null object
  - Call osMemoryPoolGetBlockSize with null object
*/
void TC_osMemoryPoolGetBlockSize_1 (void) {
#if (TC_OSMEMORYPOOLGETBLOCKSIZE_1_EN)
  osMemoryPoolId_t id;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMemoryPoolGetBlockSize to retrieve the memory block size */
  ASSERT_TRUE (osMemoryPoolGetBlockSize (id) == MEMBL_SZ);

  /* Call osMemoryPoolGetBlockSize from ISR */
  TST_IRQHandler = Irq_osMemoryPoolGetBlockSize_1;
  MemoryPoolId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == MEMBL_SZ);

  /* Call osMemoryPoolGetBlockSize from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MEMBL_SZ;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete memory pool */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolGetBlockSize with null object */
  ASSERT_TRUE (osMemoryPoolGetBlockSize (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolGetBlockSize_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLGETBLOCKSIZE_1_EN)
void Irq_osMemoryPoolGetBlockSize_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMemoryPoolGetBlockSize from ISR */
      Isr_u32 = osMemoryPoolGetBlockSize (MemoryPoolId);
      break;

    case 1:
      /* Call osMemoryPoolGetBlockSize from ISR with null object */
      Isr_u32 = osMemoryPoolGetBlockSize (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolGetCount_1
\details
  - Call osMemoryPoolGetCount to retrieve the number of memory blocks used
  - Call osMemoryPoolGetCount from ISR
  - Call osMemoryPoolGetCount from ISR with null object
  - Call osMemoryPoolGetCount with null object
*/
void TC_osMemoryPoolGetCount_1 (void) {
#if (TC_OSMEMORYPOOLGETCOUNT_1_EN)
  osMemoryPoolId_t id;
  void *p;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Allocate one block */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Call osMemoryPoolGetCount to retrieve the number of memory blocks used */
  ASSERT_TRUE (osMemoryPoolGetCount (id) == 1U);

  /* Call osMemoryPoolGetCount from ISR */
  TST_IRQHandler = Irq_osMemoryPoolGetCount_1;
  MemoryPoolId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 1U);

  /* Call osMemoryPoolGetCount from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MEMBL_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete memory pool */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolGetCount with null object */
  ASSERT_TRUE (osMemoryPoolGetCount (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolGetCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLGETCOUNT_1_EN)
void Irq_osMemoryPoolGetCount_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMemoryPoolGetCount from ISR */
      Isr_u32 = osMemoryPoolGetCount (MemoryPoolId);
      break;

    case 1:
      /* Call osMemoryPoolGetCount from ISR with null object */
      Isr_u32 = osMemoryPoolGetCount (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolGetSpace_1
\details
  - Call osMemoryPoolGetSpace to retrieve the number of available memory blocks
  - Call osMemoryPoolGetSpace from ISR
  - Call osMemoryPoolGetSpace from ISR with null object
  - Call osMemoryPoolGetSpace with null object
*/
void TC_osMemoryPoolGetSpace_1 (void) {
#if (TC_OSMEMORYPOOLGETSPACE_1_EN)
  osMemoryPoolId_t id;
  void *p;

  /* Create a memory pool */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE(id != NULL);

  /* Allocate one block */
  p = osMemoryPoolAlloc (id, 10U);
  ASSERT_TRUE (p != NULL);

  /* Call osMemoryPoolGetSpace to retrieve the number of available memory blocks */
  ASSERT_TRUE (osMemoryPoolGetSpace (id) == (MEMBL_CNT-1U));

  /* Call osMemoryPoolGetSpace from ISR */
  TST_IRQHandler = Irq_osMemoryPoolGetSpace_1;
  MemoryPoolId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == (MEMBL_CNT-1U));

  /* Call osMemoryPoolGetSpace from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MEMBL_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete memory pool */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolGetSpace with null object */
  ASSERT_TRUE (osMemoryPoolGetSpace (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolGetSpace_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLGETSPACE_1_EN)
void Irq_osMemoryPoolGetSpace_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMemoryPoolGetSpace from ISR */
      Isr_u32 = osMemoryPoolGetSpace (MemoryPoolId);
      break;

    case 1:
      /* Call osMemoryPoolGetSpace from ISR with null object */
      Isr_u32 = osMemoryPoolGetSpace (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMemoryPoolDelete_1
\details
  - Call osMemoryPoolDelete to delete a memory pool
  - Call osMemoryPoolDelete from ISR
  - Call osMemoryPoolDelete with null object
*/
void TC_osMemoryPoolDelete_1 (void) {
#if (TC_OSMEMORYPOOLDELETE_1_EN)
  osMemoryPoolId_t id;

  /* Create a memory pool object */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMemoryPoolDelete to delete a memory pool */
  ASSERT_TRUE (osMemoryPoolDelete (id) == osOK);

  /* Create a memory pool object */
  id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMemoryPoolDelete from ISR */
  TST_IRQHandler = Irq_osMemoryPoolDelete_1;
  Isr_osStatus = osOK;
  MemoryPoolId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the memory pool */
  osMemoryPoolDelete (id);

  /* Call osMemoryPoolDelete with null object */
  ASSERT_TRUE (osMemoryPoolDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMemoryPoolDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMEMORYPOOLDELETE_1_EN)
void Irq_osMemoryPoolDelete_1 (void) {
  Isr_osStatus = osMemoryPoolDelete (MemoryPoolId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MemPoolAllocAndFree
\details
- Allocate all memory blocks
- Verify that only available blocks can be allocated
- Return all memory blocks back to a memory pool
*/
void TC_MemPoolAllocAndFree (void) {
#if (TC_MEMPOOLALLOCANDFREE_EN)
  osMemoryPoolId_t MemPool_Id;
  uint32_t *mp, *addr[MEMBL_CNT];
  uint32_t  i;

  /* Create a memory pool */
  MemPool_Id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE (MemPool_Id != NULL);

  /* Clear pointer array */
  for (i = 0; i < MEMBL_CNT; i++) { addr[i] = NULL; }

  if (MemPool_Id != NULL) {

    ASSERT_TRUE (osMemoryPoolGetCapacity  (MemPool_Id) == MEMBL_CNT);
    ASSERT_TRUE (osMemoryPoolGetBlockSize (MemPool_Id) == MEMBL_SZ);

    /* - Allocate all memory blocks */
    for (i = 0; i < MEMBL_CNT; i++) {
      addr[i] = (uint32_t *)osMemoryPoolAlloc (MemPool_Id, 0);
      ASSERT_TRUE (addr[i] != NULL);
      ASSERT_TRUE (osMemoryPoolGetCount (MemPool_Id) == i+1);
      ASSERT_TRUE (osMemoryPoolGetSpace (MemPool_Id) == MEMBL_CNT-i-1);
    }
    /* - Verify that only available blocks can be allocated */
    mp = (uint32_t *)osMemoryPoolAlloc (MemPool_Id, 0);
    ASSERT_TRUE (mp == NULL);

    /* - Return all blocks back to a memory pool */
    for (i = 0; i < MEMBL_CNT; i++) {
      if (addr[i] != NULL) {
        ASSERT_TRUE (osMemoryPoolFree (MemPool_Id, addr[i]) == osOK);
        ASSERT_TRUE (osMemoryPoolGetCount (MemPool_Id) == MEMBL_CNT-i-1);
        ASSERT_TRUE (osMemoryPoolGetSpace (MemPool_Id) == i+1);
      }
    }

    /* Delete memory pool */
    ASSERT_TRUE (osMemoryPoolDelete (MemPool_Id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MemPoolAllocAndFreeComb
\details
- Allocate all memory blocks
- Verify that only available blocks can be allocated
- Return all memory blocks back to a memory pool
*/
void TC_MemPoolAllocAndFreeComb (void) {
#if (TC_MEMPOOLALLOCANDFREECOMB_EN)
  osMemoryPoolId_t MemPool_Id;
  uint32_t *addr[MEMBL_CNT];
  uint32_t i, k, set, alloc;

  /* Create a memory pool */
  MemPool_Id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE (MemPool_Id != NULL);

  ASSERT_TRUE (MEMBL_CNT <= 32);

  if (MEMBL_CNT <= 32) {
    /* - Perform pseudorandom memory allocations of available memory blocks */
    for (i = 0; i < MEMBL_CNT; i++) {
      /* Clear pointer array */
      addr [i] = 0;
    }

    for (k = 0; k < 512; k++) {
      set = LFSR_32Bit ();

      for (i = 0; i < MEMBL_CNT; i++) {
        /* If bit is set, allocate memory block else free it */
        alloc = (set & (1U << i)) ? (1) : (0);

        if (alloc) {
          if (addr[i] == 0) {
            /* Memory block is not allocated, we will do that now */
            addr[i] = (uint32_t *)osMemoryPoolAlloc (MemPool_Id, 0);
            ASSERT_TRUE (addr[i] != NULL);
          }
        }
        else {
          if (addr[i] != 0) {
            /* Memory block was allocated, we can free it */
            ASSERT_TRUE (osMemoryPoolFree (MemPool_Id, addr[i]) == osOK);
            addr [i] = 0;
          }
        }
      }
    }
    /* Free any memory block that remained allocated */
    for (i = 0; i < MEMBL_CNT; i++) {
      if (addr[i] != 0) {
        ASSERT_TRUE (osMemoryPoolFree (MemPool_Id, addr[i]) == osOK);
      }
    }
  }

  /* Delete memory pool */
  ASSERT_TRUE (osMemoryPoolDelete (MemPool_Id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MemPoolZeroInit
\details
- Allocate all memory blocks and fill them with pattern
- Return all blocks to a memory pool
- Allocate all memory blocks with osPoolCAlloc
- Check if memory was zero initialized
- Return all blocks to a memory pool
*/
void TC_MemPoolZeroInit (void) {
#if (TC_MEMPOOLZEROINIT_EN)
  osMemoryPoolId_t MemPool_Id;
  uint32_t *addr[MEMBL_CNT];
  uint32_t i, k;
  uint8_t *bp;

  /* Create a memory pool */
  MemPool_Id = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);
  ASSERT_TRUE (MemPool_Id != NULL);

  if (MemPool_Id != NULL) {
    /* Allocate all memory blocks and fill them with pattern */
    for (i = 0; i < MEMBL_CNT; i++) {
      /* Get address of the allocated memory block */
      addr[i] = osMemoryPoolAlloc (MemPool_Id, 0);
      ASSERT_TRUE (addr[i] != NULL);

      if (addr[i] != NULL) {
        bp = (uint8_t*) addr[i];

        /* Fill memory with pattern */
        for (k = 0; k < MEMBL_SZ; k++) { bp[k] = 0xAA; }
      }
    }
    /* Return all blocks to a memory pool */
    for (i = 0; i < MEMBL_CNT; i++) {
      ASSERT_TRUE (osMemoryPoolFree (MemPool_Id, addr[i]) == osOK);
    }
    ASSERT_TRUE (osMemoryPoolGetCount (MemPool_Id) == 0);
    ASSERT_TRUE (osMemoryPoolGetSpace (MemPool_Id) == MEMBL_CNT);

    /* Delete memory pool */
    ASSERT_TRUE (osMemoryPoolDelete (MemPool_Id) == osOK);
  }
#endif
}


/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MemPoolAllocation
\details
- Test memory pool object allocation
*/
void TC_MemPoolAllocation (void) {
#if (TC_MEMPOOLALLOCATION_EN)
  osMemoryPoolId_t id[MAX_MEMPOOL_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_MEMPOOL_NUM; i++) {
    id[i] = osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osMemoryPoolNew (MEMBL_CNT, MEMBL_SZ, NULL) == NULL);
  }

  osDelay(10U);

  /* Delete all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osMemoryPoolDelete(id[i]) == osOK);
  }
#endif
}

/**
@}
*/
// end of group mempool_func
