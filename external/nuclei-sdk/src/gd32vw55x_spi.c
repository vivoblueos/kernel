/*!
    \file    gd32vw55x_spi.c
    \brief   SPI driver
    
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

#include "gd32vw55x_spi.h"

/* SPI parameter initialization mask */
#define SPI_INIT_MASK                ((uint32_t)0x00003040U)

/*!
    \brief      reset SPI
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_deinit(void)
{
    /* reset SPI0 */
    rcu_periph_reset_enable(RCU_SPIRST);
    rcu_periph_reset_disable(RCU_SPIRST);
}

/*!
    \brief      initialize the parameters of SPI structure with default values
    \param[in]  none
    \param[out] spi_parameter_struct: the initialized structure spi_parameter_struct pointer
    \retval     none
*/
void spi_struct_para_init(spi_parameter_struct *spi_struct)
{
    /* configure the structure with default value */
    spi_struct->device_mode          = SPI_SLAVE;
    spi_struct->trans_mode           = SPI_TRANSMODE_FULLDUPLEX;
    spi_struct->frame_size           = SPI_FRAMESIZE_8BIT;
    spi_struct->nss                  = SPI_NSS_HARD;
    spi_struct->clock_polarity_phase = SPI_CK_PL_LOW_PH_1EDGE;
    spi_struct->prescale             = SPI_PSC_2;
    spi_struct->endian               = SPI_ENDIAN_MSB;
}

/*!
    \brief      initialize SPI parameter
    \param[in]  spi_struct: SPI parameter initialization stucture members of the structure 
                            and the member values are shown as below:
                  device_mode: SPI_MASTER, SPI_SLAVE
                  trans_mode: SPI_TRANSMODE_FULLDUPLEX, SPI_TRANSMODE_RECEIVEONLY,
                              SPI_TRANSMODE_BDRECEIVE, SPI_TRANSMODE_BDTRANSMIT
                  frame_size: SPI_FRAMESIZE_16BIT, SPI_FRAMESIZE_8BIT
                  nss: SPI_NSS_SOFT, SPI_NSS_HARD
                  endian: SPI_ENDIAN_MSB, SPI_ENDIAN_LSB
                  clock_polarity_phase: SPI_CK_PL_LOW_PH_1EDGE, SPI_CK_PL_HIGH_PH_1EDGE
                                        SPI_CK_PL_LOW_PH_2EDGE, SPI_CK_PL_HIGH_PH_2EDGE
                  prescale: SPI_PSC_n (n=2,4,8,16,32,64,128,256)
    \param[out] none
    \retval     none
*/
void spi_init(spi_parameter_struct* spi_struct)
{   
    uint32_t reg = 0U;
    reg = SPI_CTL0;
    reg &= SPI_INIT_MASK;

    /* select SPI as master or slave */
    reg |= spi_struct->device_mode;
    /* select SPI transfer mode */
    reg |= spi_struct->trans_mode;
    /* select SPI frame size */
    reg |= spi_struct->frame_size;
    /* select SPI NSS use hardware or software */
    reg |= spi_struct->nss;
    /* select SPI LSB or MSB */
    reg |= spi_struct->endian;
    /* select SPI polarity and phase */
    reg |= spi_struct->clock_polarity_phase;
    /* select SPI prescale to adjust transmit speed */
    reg |= spi_struct->prescale;

    /* write to SPI_CTL0 register */
    SPI_CTL0 = (uint32_t)reg;
}

/*!
    \brief      enable SPI
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_enable(void)
{
    SPI_CTL0 |= (uint32_t)SPI_CTL0_SPIEN;
}

/*!
    \brief      disable SPI 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_disable(void)
{
    SPI_CTL0 &= (uint32_t)(~SPI_CTL0_SPIEN);
}

/*!
    \brief      enable SPI NSS output 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_nss_output_enable(void)
{
    SPI_CTL1 |= (uint32_t)SPI_CTL1_NSSDRV;
}

/*!
    \brief      disable SPI NSS output 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_nss_output_disable(void)
{
    SPI_CTL1 &= (uint32_t)(~SPI_CTL1_NSSDRV);
}

/*!
    \brief      SPI NSS pin high level in software mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_nss_internal_high(void)
{
    SPI_CTL0 |= (uint32_t)SPI_CTL0_SWNSS;
}

/*!
    \brief      SPI NSS pin low level in software mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_nss_internal_low(void)
{
    SPI_CTL0 &= (uint32_t)(~SPI_CTL0_SWNSS);
}

/*!
    \brief      enable SPI DMA send or receive 
    \param[in]  spi_dma: SPI DMA mode
                only one parameter can be selected which is shown as below:
      \arg        SPI_DMA_TRANSMIT: SPI transmit data use DMA
      \arg        SPI_DMA_RECEIVE: SPI receive data use DMA
    \param[out] none
    \retval     none
*/
void spi_dma_enable(uint8_t spi_dma)
{
    if(SPI_DMA_TRANSMIT == spi_dma){
        SPI_CTL1 |= (uint32_t)SPI_CTL1_DMATEN;
    }else{
        SPI_CTL1 |= (uint32_t)SPI_CTL1_DMAREN;
    }
}

/*!
    \brief      disable SPI DMA send or receive 
    \param[in]  spi_dma: SPI DMA mode
                only one parameter can be selected which is shown as below:
      \arg        SPI_DMA_TRANSMIT: SPI transmit data use DMA
      \arg        SPI_DMA_RECEIVE: SPI receive data use DMA
    \param[out] none
    \retval     none
*/
void spi_dma_disable(uint8_t spi_dma)
{
    if(SPI_DMA_TRANSMIT == spi_dma){
        SPI_CTL1 &= (uint32_t)(~SPI_CTL1_DMATEN);
    }else{
        SPI_CTL1 &= (uint32_t)(~SPI_CTL1_DMAREN);
    }
}

/*!
    \brief      configure SPI data frame format
    \param[in]  frame_format: SPI frame format
                only one parameter can be selected which is shown as below:
      \arg        SPI_FRAMESIZE_16BIT: SPI frame size is 16 bits
      \arg        SPI_FRAMESIZE_8BIT: SPI frame size is 8 bits
    \param[out] none
    \retval     none
*/
void spi_data_frame_format_config(uint16_t frame_format)
{
    /* clear SPI_CTL0_FF16 bit */
    SPI_CTL0 &= (uint32_t)(~SPI_CTL0_FF16);
    /* configure SPI_CTL0_FF16 bit */
    SPI_CTL0 |= (uint32_t)frame_format;
}

/*!
    \brief      SPI transmit data
    \param[in]  data: 16-bit data
    \param[out] none
    \retval     none
*/
void spi_data_transmit(uint16_t data)
{
    SPI_DATA = (uint32_t)data;
}

/*!
    \brief      SPI receive data
    \param[in]  none
    \param[out] none
    \retval     16-bit data
*/
uint16_t spi_data_receive(void)
{
    return ((uint16_t)SPI_DATA);
}

/*!
    \brief      configure SPI bidirectional transfer direction
    \param[in]  transfer_direction: SPI transfer direction
                only one parameter can be selected which is shown as below:
      \arg        SPI_BIDIRECTIONAL_TRANSMIT: SPI work in transmit-only mode
      \arg        SPI_BIDIRECTIONAL_RECEIVE: SPI work in receive-only mode
    \param[out] none
    \retval     none
*/
void spi_bidirectional_transfer_config(uint32_t transfer_direction)
{
    if(SPI_BIDIRECTIONAL_TRANSMIT == transfer_direction){
        /* set the transmit only mode */
        SPI_CTL0 |= (uint32_t)SPI_BIDIRECTIONAL_TRANSMIT;
    }else{
        /* set the receive only mode */
        SPI_CTL0 &= SPI_BIDIRECTIONAL_RECEIVE;
    }
}

/*!
    \brief      clear TI mode format error flag status
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_format_error_clear(void)
{
    SPI_STAT = (uint32_t)(~SPI_FLAG_FERR);
}

/*!
    \brief      set SPI CRC polynomial 
    \param[in]  crc_poly: CRC polynomial value
    \param[out] none
    \retval     none
*/
void spi_crc_polynomial_set(uint16_t crc_poly)
{
    /* set SPI CRC polynomial */
    SPI_CRCPOLY = (uint32_t)crc_poly;
}

/*!
    \brief      get SPI CRC polynomial 
    \param[in]  none
    \param[out] none
    \retval     16-bit CRC polynomial
*/
uint16_t spi_crc_polynomial_get(void)
{
    return ((uint16_t)SPI_CRCPOLY);
}

/*!
    \brief      turn on CRC function 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_crc_on(void)
{
    SPI_CTL0 |= (uint32_t)SPI_CTL0_CRCEN;
}

/*!
    \brief      turn off CRC function 
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_crc_off(void)
{
    SPI_CTL0 &= (uint32_t)(~SPI_CTL0_CRCEN);
}

/*!
    \brief      SPI next data is CRC value
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_crc_next(void)
{
    SPI_CTL0 |= (uint32_t)SPI_CTL0_CRCNT;
}

/*!
    \brief      get SPI CRC send value or receive value
    \param[in]  crc: SPI crc value
                only one parameter can be selected which is shown as below:
      \arg        SPI_CRC_TX: get transmit crc value
      \arg        SPI_CRC_RX: get receive crc value
    \param[out] none
    \retval     16-bit CRC value
*/
uint16_t spi_crc_get(uint8_t crc)
{
    if(SPI_CRC_TX == crc){
        return ((uint16_t)(SPI_TCRC));
    }else{
        return ((uint16_t)(SPI_RCRC));
    }
}

/*!
    \brief      clear SPI CRC error flag status
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_crc_error_clear(void)
{
    SPI_STAT = (uint32_t)(~SPI_FLAG_CRCERR);
}

/*!
    \brief      enable SPI TI mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_ti_mode_enable(void)
{
    SPI_CTL1 |= (uint32_t)SPI_CTL1_TMOD;
}

/*!
    \brief      disable SPI TI mode
    \param[in]  none
    \param[out] none
    \retval     none
*/
void spi_ti_mode_disable(void)
{
    SPI_CTL1 &= (uint32_t)(~SPI_CTL1_TMOD);
}

/*!
    \brief      enable SPI interrupt
    \param[in]  interrupt: SPI interrupt
                only one parameter can be selected which is shown as below:
      \arg        SPI_INT_TBE: transmit buffer empty interrupt
      \arg        SPI_INT_RBNE: receive buffer not empty interrupt
      \arg        SPI_INT_ERR: CRC error,configuration error,reception overrun error
                                    and format error interrupt
    \param[out] none
    \retval     none
*/
void spi_interrupt_enable(uint8_t interrupt)
{
    switch(interrupt){
    /* SPI transmit buffer empty interrupt */
    case SPI_INT_TBE:
        SPI_CTL1 |= (uint32_t)SPI_CTL1_TBEIE;
        break;
    /* SPI receive buffer not empty interrupt */
    case SPI_INT_RBNE:
        SPI_CTL1 |= (uint32_t)SPI_CTL1_RBNEIE;
        break;
    /* SPI error */
    case SPI_INT_ERR:
        SPI_CTL1 |= (uint32_t)SPI_CTL1_ERRIE;
        break;
    default:
        break;
    }
}

/*!
    \brief      disable SPI interrupt
    \param[in]  interrupt: SPI interrupt
                only one parameter can be selected which is shown as below:
      \arg        SPI_INT_TBE: transmit buffer empty interrupt
      \arg        SPI_INT_RBNE: receive buffer not empty interrupt
      \arg        SPI_INT_ERR: CRC error,configuration error,reception overrun error
                                    and format error interrupt
    \param[out] none
    \retval     none
*/
void spi_interrupt_disable(uint8_t interrupt)
{
    switch(interrupt){
    /* SPI transmit buffer empty interrupt */
    case SPI_INT_TBE:
        SPI_CTL1 &= (uint32_t)(~SPI_CTL1_TBEIE);
        break;
    /* SPI receive buffer not empty interrupt */
    case SPI_INT_RBNE:
        SPI_CTL1 &= (uint32_t)(~SPI_CTL1_RBNEIE);
        break;
    /* SPI error */
    case SPI_INT_ERR:
        SPI_CTL1 &= (uint32_t)(~SPI_CTL1_ERRIE);
        break;
    default :
        break;
    }
}

/*!
    \brief      get SPI interrupt flag status
    \param[in]  interrupt: SPI interrupt flag status
                only one parameter can be selected which is shown as below:
      \arg        SPI_INT_FLAG_TBE: transmit buffer empty interrupt flag
      \arg        SPI_INT_FLAG_RBNE: receive buffer not empty interrupt flag
      \arg        SPI_INT_FLAG_RXORERR: overrun interrupt flag
      \arg        SPI_INT_FLAG_CONFERR: configuration error interrupt flag
      \arg        SPI_INT_FLAG_CRCERR: CRC error interrupt flag
      \arg        SPI_INT_FLAG_FERR: format error interrupt flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus spi_interrupt_flag_get(uint8_t interrupt)
{
    uint32_t reg1 = SPI_STAT;
    uint32_t reg2 = SPI_CTL1;

    switch(interrupt){
    /* SPI transmit buffer empty interrupt */
    case SPI_INT_FLAG_TBE:
        reg1 = reg1 & SPI_STAT_TBE;
        reg2 = reg2 & SPI_CTL1_TBEIE;
        break;
    /* SPI receive buffer not empty interrupt */
    case SPI_INT_FLAG_RBNE:
        reg1 = reg1 & SPI_STAT_RBNE;
        reg2 = reg2 & SPI_CTL1_RBNEIE;
        break;
    /* SPI overrun interrupt */
    case SPI_INT_FLAG_RXORERR:
        reg1 = reg1 & SPI_STAT_RXORERR;
        reg2 = reg2 & SPI_CTL1_ERRIE;
        break;
    /* SPI configuration error interrupt */
    case SPI_INT_FLAG_CONFERR:
        reg1 = reg1 & SPI_STAT_CONFERR;
        reg2 = reg2 & SPI_CTL1_ERRIE;
        break;
    /* SPI CRC error interrupt */
    case SPI_INT_FLAG_CRCERR:
        reg1 = reg1 & SPI_STAT_CRCERR;
        reg2 = reg2 & SPI_CTL1_ERRIE;
        break;
    /* SPI format error interrupt */
    case SPI_INT_FLAG_FERR:
        reg1 = reg1 & SPI_STAT_FERR;
        reg2 = reg2 & SPI_CTL1_ERRIE;
        break;
    default :
        break;
    }
    /*get SPI interrupt flag status */
    if((0U != reg1) && (0U != reg2)){
        return SET;
    }else{
        return RESET;
    }
}

/*!
    \brief      get SPI flag status
    \param[in]  flag: SPI flag status
                only one parameter can be selected which is shown as below:
      \arg        SPI_FLAG_TBE: transmit buffer empty flag
      \arg        SPI_FLAG_RBNE: receive buffer not empty flag
      \arg        SPI_FLAG_TRANS: transmit on-going flag
      \arg        SPI_FLAG_RXORERR: receive overrun error flag
      \arg        SPI_FLAG_CONFERR: mode configuration error flag
      \arg        SPI_FLAG_CRCERR: CRC error flag
      \arg        SPI_FLAG_FERR: format error flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus spi_flag_get(uint32_t flag)
{
    if(0U != (SPI_STAT & flag)){
        return SET;
    }else{
        return RESET;
    }
}
