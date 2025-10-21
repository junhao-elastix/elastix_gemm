// ------------------------------------------------------------------
//
// Copyright (c) 2021 Achronix Semiconductor Corp.
// All Rights Reserved.
//
// This Software constitutes an unpublished work and contains
// valuable proprietary information and trade secrets belonging
// to Achronix Semiconductor Corp.
//
// Permission is hereby granted to use this Software including
// without limitation the right to copy, modify, merge or distribute
// copies of the software subject to the following condition:
//
// The above copyright notice and this permission notice shall
// be included in in all copies of the Software.
//
// The Software is provided “as is” without warranty of any kind
// expressed or implied, including  but not limited to the warranties
// of merchantability fitness for a particular purpose and non-infringement.
// In no event shall the copyright holder be liable for any claim,
// damages, or other liability for any damages or other liability,
// whether an action of contract, tort or otherwise, arising from, 
// out of, or in connection with the Software
//
// ------------------------------------------------------------------
// VectorPath rev 1 LEDs
//   There are 4 bi-colour LEDs controlled by 8-bits
//   The pairs of bits per LED are [7,3], [6,2], [5,1], [4,0]
//   Within these pairs, the bit patterns below define the colour displayed
// ------------------------------------------------------------------

// These parameters can be included multiple times in a compilation as they
// are local to the individual files that include this header file
localparam [1:0] ACX_VP_LED_OFF    = 2'b11;
localparam [1:0] ACX_VP_LED_GREEN  = 2'b10;
localparam [1:0] ACX_VP_LED_ORANGE = 2'b01;
localparam [1:0] ACX_VP_LED_YELLOW = 2'b00;

