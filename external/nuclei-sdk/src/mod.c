// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "gd32vw55x.h"

// FIXME: We're not using nesting interrupt handling at present.
static void init_swi() { eclic_irq_enable(CLIC_INT_SFT, 0, 0); }

static void init_timer()
{
  SysTimer_SetCompareValue(SystemCoreClock / 4000);
  __ECLIC_SetTrigIRQ(CLIC_INT_TMR, ECLIC_POSTIVE_EDGE_TRIGGER);
  eclic_irq_enable(CLIC_INT_TMR, 0, 0);
}

void init_soc()
{
  SystemInit();
  EnableICache();
  init_swi();
  init_timer();
  rcu_periph_clock_enable(RCU_GPIOB);
  rcu_periph_clock_enable(RCU_GPIOA);

  /* enable USART clock */
  rcu_periph_clock_enable(RCU_USART0);
}
