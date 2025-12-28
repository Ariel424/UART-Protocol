// Asynchronous FIFO Module
module ASYNC_FIFO #(parameter DATA_WIDTH = 8, ADDR_WIDTH = 4) (
    // Write clock domain
    input                    WClk,
    input                    WReset,
    input                    Write,
    input  [DATA_WIDTH-1:0]  Din,
    output                   Full,
    
    // Read clock domain  
    input                    RClk,
    input                    RReset,
    input                    Read,
    output reg [DATA_WIDTH-1:0] Dout,
    output                   Empty
);

  localparam DEPTH = 1 << ADDR_WIDTH;
  
  // Memory array
  reg [DATA_WIDTH-1:0] Mem [0:DEPTH-1];
  
  // Write domain signals
  reg [ADDR_WIDTH:0] Write_Pointer = 0;
  reg [ADDR_WIDTH:0] Write_Pointer_Gray = 0;
  reg [ADDR_WIDTH:0] Read_Pointer_Gray_Sync1 = 0;
  reg [ADDR_WIDTH:0] Read_Pointer_Gray_Sync2 = 0;
  
  // Read domain signals
  reg [ADDR_WIDTH:0] Read_Pointer = 0;
  reg [ADDR_WIDTH:0] Read_Pointer_Gray = 0;
  reg [ADDR_WIDTH:0] Write_Pointer_Gray_Sync1 = 0;
  reg [ADDR_WIDTH:0] Write_Pointer_Gray_Sync2 = 0;
  
  // Binary to Gray code conversion function
  function [ADDR_WIDTH:0] bin2gray;
    input [ADDR_WIDTH:0] binary;
    begin
      bin2gray = binary ^ (binary >> 1);
    end
  endfunction
  
  // Gray to Binary code conversion function
  function [ADDR_WIDTH:0] gray2bin;
    input [ADDR_WIDTH:0] gray;
    integer i;
    begin
      gray2bin[ADDR_WIDTH] = gray[ADDR_WIDTH];
      for (i = ADDR_WIDTH-1; i >= 0; i = i-1)
        gray2bin[i] = gray2bin[i+1] ^ gray[i];
    end
  endfunction
  
  //===========================================
  // WRITE CLOCK DOMAIN
  //===========================================
  
  // Write pointer and Gray code generation
  always @(posedge WClk or posedge WReset) begin
    if (WReset) begin
      Write_Pointer <= 0;
      Write_Pointer_Gray <= 0;
    end
    else if (Write && !Full) begin
      Write_Pointer <= Write_Pointer + 1;
      Write_Pointer_Gray <= bin2gray(Write_Pointer + 1);
    end
  end
  
  // Write to memory
  always @(posedge WClk) begin
    if (Write && !Full)
      Mem[Write_Pointer[ADDR_WIDTH-1:0]] <= Din;
  end
  
  // Synchronize read pointer to write clock domain (2-stage)
  always @(posedge WClk or posedge WReset) begin
    if (WReset) begin
      Read_Pointer_Gray_Sync1 <= 0;
      Read_Pointer_Gray_Sync2 <= 0;
    end
    else begin
      Read_Pointer_Gray_Sync1 <= Read_Pointer_Gray;
      Read_Pointer_Gray_Sync2 <= Read_Pointer_Gray_Sync1;
    end
  end
  
  // Full flag generation
  assign Full = (Write_Pointer_Gray == {~Read_Pointer_Gray_Sync2[ADDR_WIDTH:ADDR_WIDTH-1], 
                                         Read_Pointer_Gray_Sync2[ADDR_WIDTH-2:0]});
  
  //===========================================
  // READ CLOCK DOMAIN
  //===========================================
  
  // Read pointer and Gray code generation
  always @(posedge RClk or posedge RReset) begin
    if (RReset) begin
      Read_Pointer <= 0;
      Read_Pointer_Gray <= 0;
    end
    else if (Read && !Empty) begin
      Read_Pointer <= Read_Pointer + 1;
      Read_Pointer_Gray <= bin2gray(Read_Pointer + 1);
    end
  end
  
  // Read from memory
  always @(posedge RClk) begin
    if (Read && !Empty)
      Dout <= Mem[Read_Pointer[ADDR_WIDTH-1:0]];
  end
  
  // Synchronize write pointer to read clock domain (2-stage)
  always @(posedge RClk or posedge RReset) begin
    if (RReset) begin
      Write_Pointer_Gray_Sync1 <= 0;
      Write_Pointer_Gray_Sync2 <= 0;
    end
    else begin
      Write_Pointer_Gray_Sync1 <= Write_Pointer_Gray;
      Write_Pointer_Gray_Sync2 <= Write_Pointer_Gray_Sync1;
    end
  end
  
  // Empty flag generation
  assign Empty = (Read_Pointer_Gray == Write_Pointer_Gray_Sync2);

endmodule

//===========================================
// INTERFACE FOR TESTBENCH
//===========================================

interface ASYNC_FIFO_if;
  
  // Write clock domain
  logic WClk;
  logic WReset;
  logic Write;
  logic [7:0] Data_in;
  logic Full;
  
  // Read clock domain
  logic RClk;
  logic RReset;
  logic Read;
  logic [7:0] Data_out;
  logic Empty;
  
endinterface
