/*!
    \file    gd32vw55x_qspi.h
    \brief   definitions for the QSPI

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

#ifndef GD32VW55X_QSPI_H
#define GD32VW55X_QSPI_H

#include "gd32vw55x.h"

/* QSPI definitions */
#define QSPI                              QSPI_REG_BASE

/* registers definitions */
#define QSPI_CTL                          REG32(QSPI + 0x00000000U)            /*!< QSPI control register */
#define QSPI_DCFG                         REG32(QSPI + 0x00000004U)            /*!< QSPI device configuration register */
#define QSPI_STAT                         REG32(QSPI + 0x00000008U)            /*!< QSPI status register */
#define QSPI_STATC                        REG32(QSPI + 0x0000000CU)            /*!< QSPI status clear register */
#define QSPI_DTLEN                        REG32(QSPI + 0x00000010U)            /*!< QSPI data length register */
#define QSPI_TCFG                         REG32(QSPI + 0x00000014U)            /*!< QSPI transfer configuration register */
#define QSPI_ADDR                         REG32(QSPI + 0x00000018U)            /*!< QSPI address register */
#define QSPI_ALTE                         REG32(QSPI + 0x0000001CU)            /*!< QSPI alternate bytes register */
#define QSPI_DATA                         REG32(QSPI + 0x00000020U)            /*!< QSPI data register */
#define QSPI_STATMK                       REG32(QSPI + 0x00000024U)            /*!< QSPI status mask register */
#define QSPI_STATMATCH                    REG32(QSPI + 0x00000028U)            /*!< QSPI status match register */
#define QSPI_INTERVAL                     REG32(QSPI + 0x0000002CU)            /*!< QSPI interval register */
#define QSPI_TMOUT                        REG32(QSPI + 0x00000030U)            /*!< QSPI timeout register */
#define QSPI_FLUSH                        REG32(QSPI + 0x00000034U)            /*!< QSPI FIFO flush register */

/* bits definitions */
/* QSPI_CTL */
#define QSPI_CTL_QSPIEN                   BIT(0)                               /*!< enable QSPI */
#define QSPI_CTL_ABORT                    BIT(1)                               /*!< abort request */
#define QSPI_CTL_DMAEN                    BIT(2)                               /*!< enable DMA */
#define QSPI_CTL_TMOUTEN                  BIT(3)                               /*!< timeout counter enable */
#define QSPI_CTL_SSAMPLE                  BITS(4,5)                            /*!< sample shift */
#define QSPI_CTL_SCKDEN                   BIT(6)                               /*!< sck delay enable */
#define QSPI_CTL_FTL                      BITS(8,11)                           /*!< fifo threshold level */
#define QSPI_CTL_SCKDVALUE                BITS(12,15)                          /*!< sck delay vlaue */
#define QSPI_CTL_TERRIE                   BIT(16)                              /*!< enable transfer error interrupt */
#define QSPI_CTL_TCIE                     BIT(17)                              /*!< enable transfer complete interrupt */
#define QSPI_CTL_FTIE                     BIT(18)                              /*!< enable fifo threshold interrupt */
#define QSPI_CTL_RPMFIE                   BIT(19)                              /*!< enable read polling mode match interrupt */
#define QSPI_CTL_TMOUTIE                  BIT(20)                              /*!< enable timeout interrupt */
#define QSPI_CTL_RPMS                     BIT(22)                              /*!< read polling mode stop */
#define QSPI_CTL_RPMM                     BIT(23)                              /*!< read polling match mode */
#define QSPI_CTL_PSC                      BITS(24,31)                          /*!< prescaler */

/* QSPI_DCFG */
#define QSPI_DCFG_CKMOD                   BIT(0)                               /*!< this bit indicates the sck level when qspi is free */
#define QSPI_DCFG_CSHC                    BITS(8,10)                           /*!< chip select high cycle */
#define QSPI_DCFG_FMSZ                    BITS(16,20)                          /*!< flash memory size */

/* QSPI_STAT */
#define QSPI_STAT_TERR                    BIT(0)                               /*!< transfer error flag */
#define QSPI_STAT_TC                      BIT(1)                               /*!< transfer complete flag */
#define QSPI_STAT_FT                      BIT(2)                               /*!< fifo threshold flag */
#define QSPI_STAT_RPMF                    BIT(3)                               /*!< read polling match flag */
#define QSPI_STAT_TMOUT                   BIT(4)                               /*!< timeout flag */
#define QSPI_STAT_BUSY                    BIT(5)                               /*!< busy flag */
#define QSPI_STAT_FL                      BITS(8,12)                           /*!< FIFO level */

/* QSPI_STATC */
#define QSPI_STATC_TERRC                  BIT(0)                               /*!< clear transfer error flag */
#define QSPI_STATC_TCC                    BIT(1)                               /*!< clear transfer complete flag */
#define QSPI_STATC_RPMFC                  BIT(3)                               /*!< clear read polling mode match flag */
#define QSPI_STATC_TMOUTC                 BIT(4)                               /*!< clear timeout flag */

/* QSPI_DTLEN */
#define QSPI_DTLEN_DTLEN                  BITS(0,31)                           /*!< data length */

/* QSPI_TCFG */
#define QSPI_TCFG_INSTRUCTION             BITS(0,7)                            /*!< command information to be send to the flash memory */
#define QSPI_TCFG_IMOD                    BITS(8,9)                            /*!< instruction mode */
#define QSPI_TCFG_ADDRMOD                 BITS(10,11)                          /*!< address mode */
#define QSPI_TCFG_ADDRSZ                  BITS(12,13)                          /*!< address size */
#define QSPI_TCFG_ALTEMOD                 BITS(14,15)                          /*!< alternate bytes mode */
#define QSPI_TCFG_ALTESZ                  BITS(16,17)                          /*!< alternate bytes size */
#define QSPI_TCFG_DUMYC                   BITS(18,22)                          /*!< number of dummy cycles */
#define QSPI_TCFG_DATAMOD                 BITS(24,25)                          /*!< data mode */
#define QSPI_TCFG_FMOD                    BITS(26,27)                          /*!< functional mode */
#define QSPI_TCFG_SIOO                    BIT(28)                              /*!< send instruction only once */

/* QSPI_ADDR */
#define QSPI_ADDR_ADDR                    BITS(0,31)                           /*!< address to be send to the external flash memory */

/* QSPI_ALTE */
#define QSPI_ALTE_ALTE                    BITS(0,31)                           /*!< optional data to be send to the flash memory */

/* QSPI_DATA */
#define QSPI_DATA_DATA                    BITS(0,31)                           /*!< data to be transferred through the flash memory */

/* QSPI_STATMK */
#define QSPI_STATMK_MASK                  BITS(0,31)                           /*!< status mask */

/* QSPI_STATMATCH */
#define QSPI_STATMATCH_MATCH              BITS(0,31)                           /*!< status match */

/* QSPI_INTERVAL */
#define QSPI_INTERVAL_INTERVAL            BITS(0,15)                           /*!< interval cycle */

/* QSPI_TMOUT */
#define QSPI_TMOUT_TMOUTCYC               BITS(0,15)                           /*!< timeout cycle */

/* QSPI_FLUSH */
#define QSPI_FLUSH_FLUSH                  BIT(0)                               /*!< used to flush all QSPI interval FIFO */

/* constants definitions */
/* QSPI initialize structure definitions */
typedef struct {
    uint32_t prescaler;                                                        /*!< specifies the prescaler factor for generating clock based on the AHB clock.
                                                                                    this parameter can be a number between 0 and 255 */
    uint32_t fifo_threshold;                                                   /*!< specifies the threshold number of bytes in the FIFO (used only in normal mode)
                                                                                    this parameter can be a value between 1 and 16 */
    uint32_t sample_shift;                                                     /*!< specifies the sample shift. the data is sampled 1/2 clock cycle delay later to
                                                                                    take in account external signal delays */
    uint32_t flash_size;                                                       /*!< specifies the flash size. flash_size+1 is effectively the number of address bits
                                                                                    required to address the flash memory. The flash capacity can be up to 4GB
                                                                                    (addressed using 32 bits) in normal mode, but the addressable space in
                                                                                    memory mapped mode is limited to 128MB
                                                                                    this parameter can be a number between 0 and 31 */
    uint32_t cs_high_time;                                                     /*!< specifies the chip select high time. cs_high_time+1 defines the minimum number
                                                                                    of clock cycles which the chip select must remain high between commands */
    uint32_t clock_mode;                                                       /*!< specifies the clock mode. it indicates the level that clock takes between commands */
} qspi_init_struct;

/* QSPI command structure definitions */
typedef struct {
    uint32_t instruction_mode;                                                 /*!< specifies the instruction mode */
    uint32_t instruction;                                                      /*!< specifies the instruction to be sent
                                                                                    this parameter can be a value (8-bit) between 0x00 and 0xFF */
    uint32_t addr_mode;                                                        /*!< specifies the address mode */
    uint32_t addr_size;                                                        /*!< specifies the address size */
    uint32_t addr;                                                             /*!< specifies the address to be sent (Size from 1 to 4 bytes according addr_size)
                                                                                    this parameter can be a value (32-bits) between 0x0 and 0xFFFFFFFF */
    uint32_t altebytes_mode;                                                   /*!< specifies the alternate bytes mode */
    uint32_t altebytes_size;                                                   /*!< specifies the alternate bytes size */
    uint32_t altebytes;                                                        /*!< specifies the alternate Bytes to be sent (size from 1 to 4 bytes according altebytes_size)
                                                                                    this parameter can be a value (32-bits) between 0x0 and 0xFFFFFFFF */
    uint32_t dummycycles;                                                      /*!< specifies the number of dummy cycles.
                                                                                    this parameter can be a number between 0 and 31 */
    uint32_t data_mode;                                                        /*!< specifies the data mode (used for dummy cycles and data phases) */
    uint32_t data_length;                                                      /*!< specifies the number of data to transfer. (this is the number of bytes)
                                                                                    this parameter can be any value between 0 and 0xFFFFFFFF (0 means undefined length
                                                                                    until end of memory) */
    uint32_t sioo_mode;                                                        /*!< specifies the send instruction only once mode */
} qspi_command_struct;

/* QSPI read polling structure definitions */
typedef struct {
    uint32_t match;                                                            /*!< specifies the value to be compared with the masked status register to get a match.
                                                                                    this parameter can be any value between 0 and 0xFFFFFFFF */
    uint32_t mask;                                                             /*!< specifies the mask to be applied to the status bytes received.
                                                                                    this parameter can be any value between 0 and 0xFFFFFFFF */
    uint32_t interval;                                                         /*!< specifies the number of clock cycles between two read during read polling phases.
                                                                                    this parameter can be any value between 0 and 0xFFFF */
    uint32_t statusbytes_size;                                                 /*!< specifies the size of the status bytes received.
                                                                                    this parameter can be any value between 1 and 4 */
    uint32_t match_mode;                                                       /*!< specifies the method used for determining a match. */
    uint32_t polling_stop;                                                     /*!< specifies if read polling is stopped after a match. */
} qspi_polling_struct;

/* QSPI clock mode */
#define QSPI_CLOCK_MODE_0                 ((uint32_t)0x00000000U)              /*!< QSPI clock mode 0 */
#define QSPI_CLOCK_MODE_3                 QSPI_DCFG_CKMOD                      /*!< QSPI clock mode 3 */

/* QSPI sample shift */
#define CTL_SSAMPLE(regval)               (BITS(4,5) & ((uint32_t)(regval) << 4))
#define QSPI_SAMPLE_SHIFTING_NONE         CTL_SSAMPLE(0)                       /*!< no shift when sample data */
#define QSPI_SAMPLE_SHIFTING_HALFCYCLE    CTL_SSAMPLE(1)                       /*!< 1/2 sck cycle shift when sample data */
#define QSPI_SAMPLE_SHIFTING_ONECYCLE     CTL_SSAMPLE(2)                       /*!< one sck cycle shift when sample data */

/* QSPI chip select high cycle */
#define DCFG_CSHC(regval)                 (BITS(8,10) & ((uint32_t)(regval) << 8))
#define QSPI_CS_HIGH_TIME_1_CYCLE         DCFG_CSHC(0)                         /*!< QSPI CS stays high for at least 1 cycle */
#define QSPI_CS_HIGH_TIME_2_CYCLE         DCFG_CSHC(1)                         /*!< QSPI CS stays high for at least 2 cycles */
#define QSPI_CS_HIGH_TIME_3_CYCLE         DCFG_CSHC(2)                         /*!< QSPI CS stays high for at least 3 cycles */
#define QSPI_CS_HIGH_TIME_4_CYCLE         DCFG_CSHC(3)                         /*!< QSPI CS stays high for at least 4 cycles */
#define QSPI_CS_HIGH_TIME_5_CYCLE         DCFG_CSHC(4)                         /*!< QSPI CS stays high for at least 5 cycles */
#define QSPI_CS_HIGH_TIME_6_CYCLE         DCFG_CSHC(5)                         /*!< QSPI CS stays high for at least 6 cycles */
#define QSPI_CS_HIGH_TIME_7_CYCLE         DCFG_CSHC(6)                         /*!< QSPI CS stays high for at least 7 cycles */
#define QSPI_CS_HIGH_TIME_8_CYCLE         DCFG_CSHC(7)                         /*!< QSPI CS stays high for at least 8 cycles */

/* QSPI instruction mode */
#define TCFG_IMODE(regval)                (BITS(8,9) & ((uint32_t)(regval) << 8))
#define QSPI_INSTRUCTION_NONE             TCFG_IMODE(0)                        /*!< no instruction */
#define QSPI_INSTRUCTION_1_LINE           TCFG_IMODE(1)                        /*!< instruction on a single line */
#define QSPI_INSTRUCTION_2_LINES          TCFG_IMODE(2)                        /*!< instruction on two lines */
#define QSPI_INSTRUCTION_4_LINES          TCFG_IMODE(3)                        /*!< instruction on four lines */

/* QSPI address mode */
#define TCFG_ADDRMOD(regval)              (BITS(10,11) & ((uint32_t)(regval) << 10))
#define QSPI_ADDR_NONE                    TCFG_ADDRMOD(0)                      /*!< no address */
#define QSPI_ADDR_1_LINE                  TCFG_ADDRMOD(1)                      /*!< address on a single line */
#define QSPI_ADDR_2_LINES                 TCFG_ADDRMOD(2)                      /*!< address on two lines */
#define QSPI_ADDR_4_LINES                 TCFG_ADDRMOD(3)                      /*!< address on four lines */

/* QSPI address size */
#define TCFG_ADDRSZ(regval)               (BITS(12,13) & ((uint32_t)(regval) << 12))
#define QSPI_ADDR_8_BITS                  TCFG_ADDRSZ(0)                       /*!< 8 bits address */
#define QSPI_ADDR_16_BITS                 TCFG_ADDRSZ(1)                       /*!< 16 bits address */
#define QSPI_ADDR_24_BITS                 TCFG_ADDRSZ(2)                       /*!< 24 bits address */
#define QSPI_ADDR_32_BITS                 TCFG_ADDRSZ(3)                       /*!< 32 bits address */

/* QSPI alternate bytes mode */
#define TCFG_ALTEMOD(regval)              (BITS(14,15) & ((uint32_t)(regval) << 14))
#define QSPI_ALTE_BYTES_NONE              TCFG_ALTEMOD(0)                      /*!< no alternate bytes */
#define QSPI_ALTE_BYTES_1_LINE            TCFG_ALTEMOD(1)                      /*!< alternate bytes on a single line */
#define QSPI_ALTE_BYTES_2_LINES           TCFG_ALTEMOD(2)                      /*!< alternate bytes on two lines */
#define QSPI_ALTE_BYTES_4_LINES           TCFG_ALTEMOD(3)                      /*!< alternate bytes on four lines */

/* QSPI alternate bytes size */
#define TCFG_ALTESZ(regval)               (BITS(16,17) & ((uint32_t)(regval) << 16))
#define QSPI_ALTE_BYTES_8_BITS            TCFG_ALTESZ(0)                       /*!< 8 bits alternate byte */
#define QSPI_ALTE_BYTES_16_BITS           TCFG_ALTESZ(1)                       /*!< 16 bits alternate bytes */
#define QSPI_ALTE_BYTES_24_BITS           TCFG_ALTESZ(2)                       /*!< 24 bits alternate bytes */
#define QSPI_ALTE_BYTES_32_BITS           TCFG_ALTESZ(3)                       /*!< 32 bits alternate bytes */

/* QSPI data mode */
#define TCFG_DATAMOD(regval)              (BITS(24,25) & ((uint32_t)(regval) << 24))
#define QSPI_DATA_NONE                    TCFG_DATAMOD(0)                      /*!< no data */
#define QSPI_DATA_1_LINE                  TCFG_DATAMOD(1)                      /*!< data on a single line */
#define QSPI_DATA_2_LINES                 TCFG_DATAMOD(2)                      /*!< data on two lines */
#define QSPI_DATA_4_LINES                 TCFG_DATAMOD(3)                      /*!< data on four lines */

/* QSPI functional mode */
#define TCFG_FMOD(regval)                 (BITS(26,27) & ((uint32_t)(regval) << 26))
#define QSPI_NORMAL_WRITE                 TCFG_FMOD(0)                         /*! < normal write mode */
#define QSPI_NORMAL_READ                  TCFG_FMOD(1)                         /*! < normal read mode */
#define QSPI_READ_POLLING                 TCFG_FMOD(2)                         /*! < read polling mode */
#define QSPI_MEMORY_MAPPED                TCFG_FMOD(3)                         /*! < memory mapped mode */

/* QSPI sioo mode */
#define QSPI_SIOO_INST_EVERY_CMD          ((uint32_t)0x00000000U)              /*!< send instruction on every command sequence */
#define QSPI_SIOO_INST_ONLY_FIRST_CMD     QSPI_TCFG_SIOO                       /*!< send instruction only for the first command sequence */

/* QSPI timeout count */
#define QSPI_TMOUT_DISABLE                ((uint32_t)0x00000000U)              /*!< disable timeout counter */
#define QSPI_TMOUT_ENABLE                 QSPI_CTL_TMOUTEN                     /*!< enable timeout counter */

/* QSPI match mode */
#define QSPI_MATCH_MODE_AND               ((uint32_t)0x00000000U)              /*!< AND match mode */
#define QSPI_MATCH_MODE_OR                QSPI_CTL_RPMM                        /*!< OR match mode */

/* QSPI read polling stop */
#define QSPI_POLLING_STOP_DISABLE         ((uint32_t)0x00000000U)              /*!< disable read polling mode stop */
#define QSPI_POLLING_STOP_ENABLE          QSPI_CTL_RPMS                        /*!< enable read polling mode stop */

/* QSPI interrupt */
#define QSPI_INT_TC                       QSPI_CTL_TCIE                        /*!< transfer complete interrupt */
#define QSPI_INT_FT                       QSPI_CTL_FTIE                        /*!< FIFO threshold interrupt */
#define QSPI_INT_TERR                     QSPI_CTL_TERRIE                      /*!< transfer error interrupt */
#define QSPI_INT_RPMF                     QSPI_CTL_RPMFIE                      /*!< read polling match interrupt */
#define QSPI_INT_TMOUT                    QSPI_CTL_TMOUTIE                     /*!< timeout interrupt */

/* QSPI flag definitions */
#define QSPI_FLAG_BUSY                    QSPI_STAT_BUSY                       /*!< busy flag */
#define QSPI_FLAG_TERR                    QSPI_STAT_TERR                       /*!< transfer error flag */
#define QSPI_FLAG_TC                      QSPI_STAT_TC                         /*!< transfer complete flag */
#define QSPI_FLAG_FT                      QSPI_STAT_FT                         /*!< fifo threshold flag */
#define QSPI_FLAG_RPMF                    QSPI_STAT_RPMF                       /*!< read polling match flag */
#define QSPI_FLAG_TMOUT                   QSPI_STAT_TMOUT                      /*!< timeout flag */

/* QSPI interrupt flag definitions */
#define QSPI_INT_FLAG_TERR                QSPI_STAT_TERR                       /*!< transfer error interrupt flag */
#define QSPI_INT_FLAG_TC                  QSPI_STAT_TC                         /*!< transfer complete interrupt flag */
#define QSPI_INT_FLAG_FT                  QSPI_STAT_FT                         /*!< fifo threshold interrupt flag */
#define QSPI_INT_FLAG_RPMF                QSPI_STAT_RPMF                       /*!< read polling match interrupt flag */
#define QSPI_INT_FLAG_TMOUT               QSPI_STAT_TMOUT                      /*!< timeout interrupt flag */

/* function declarations */
/* initialization functions */
/* reset QSPI */
void qspi_deinit(void);
/* initialize the parameters of QSPI init structure with the default values */
void qspi_struct_para_init(qspi_init_struct *init_para);
/* initialize the parameters of QSPI command structure with the default values */
void qspi_cmd_struct_para_init(qspi_command_struct *init_para);
/* initialize the parameters of QSPI read polling structure with the default values */
void qspi_polling_struct_para_init(qspi_polling_struct *init_para);
/* initialize QSPI */
void qspi_init(qspi_init_struct *qspi_struct);
/* enable QSPI */
void qspi_enable(void);
/* disable QSPI */
void qspi_disable(void);
/* enable QSPI DMA */
void qspi_dma_enable(void);
/* disable QSPI DMA */
void qspi_dma_disable(void);

/* application function declarations */
/* configure QSPI command parameters */
void qspi_command_config(qspi_command_struct *cmd);
/* configure QSPI read polling mode */
void qspi_polling_config(qspi_command_struct *cmd, qspi_polling_struct *cfg);
/* configure QSPI memory mapped mode */
void qspi_memorymapped_config(qspi_command_struct *cmd, uint16_t timeout, uint32_t toen);
/* QSPI transmit data function */
void qspi_data_transmit(uint8_t *tdata);
/* QSPI receive data function */
void qspi_data_receive(uint8_t *rdata);
/* abort the current transmission */
void qspi_transmission_abort(void);

/* interrupt & flag functions */
/* get QSPI flag status */
FlagStatus qspi_flag_get(uint32_t flag);
/* clear QSPI flag status */
void qspi_flag_clear(uint32_t flag);
/* enable QSPI interrupt */
void qspi_interrupt_enable(uint32_t interrupt);
/* disable QSPI interrupt */
void qspi_interrupt_disable(uint32_t interrupt);
/* get QSPI interrupt flag status */
FlagStatus qspi_interrupt_flag_get(uint32_t int_flag);
/* clear QSPI interrupt flag status */
void qspi_interrupt_flag_clear(uint32_t int_flag);

#endif /* GD32VW55X_QSPI_H */
