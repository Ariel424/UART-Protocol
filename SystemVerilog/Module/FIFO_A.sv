// Asynchronous FIFO Module
module ASYNC_FIFO (
    // Write clock domain
    input WClk,
    input WReset,
    input Write,
    input [7:0] Din,
    output Full,
    
    // Read clock domain  
    input RClk,
    input RReset,
    input Read,
    output reg [7:0] Dout,
    output Empty
);

  // Memory array
  reg [7:0] Mem [15:0];
  
  // Write domain signals
  reg [4:0] Write_Pointer = 0;
  reg [4:0] Write_Pointer_Gray = 0;
  reg [4:0] Read_Pointer_Gray_Sync1 = 0;
  reg [4:0] Read_Pointer_Gray_Sync2 = 0;
  
  // Read domain signals
  reg [4:0] Read_Pointer = 0;
  reg [4:0] Read_Pointer_Gray = 0;
  reg [4:0] Write_Pointer_Gray_Sync1 = 0;
  reg [4:0] Write_Pointer_Gray_Sync2 = 0;
  
  // Binary to Gray code conversion
  function [4:0] bin2gray;
    input [4:0] binary;
    begin
      bin2gray = binary ^ (binary >> 1);
    end
  endfunction
  
  // Write pointer and Gray code
  always @(posedge WClk) begin
    if (WReset == 1'b1) begin
      Write_Pointer <= 0;
      Write_Pointer_Gray <= 0;
    end
    else if (Write && !Full) begin
      Mem[Write_Pointer[3:0]] <= Din;
      Write_Pointer <= Write_Pointer + 1;
      Write_Pointer_Gray <= bin2gray(Write_Pointer + 1);
    end
  end
  
  // Synchronize read pointer to write clock domain
  always @(posedge WClk) begin
    if (WReset == 1'b1) begin
      Read_Pointer_Gray_Sync1 <= 0;
      Read_Pointer_Gray_Sync2 <= 0;
    end
    else begin
      Read_Pointer_Gray_Sync1 <= Read_Pointer_Gray;
      Read_Pointer_Gray_Sync2 <= Read_Pointer_Gray_Sync1;
    end
  end
  
  // Read pointer and Gray code
  always @(posedge RClk) begin
    if (RReset == 1'b1) begin
      Read_Pointer <= 0;
      Read_Pointer_Gray <= 0;
    end
    else if (Read && !Empty) begin
      Dout <= Mem[Read_Pointer[3:0]];
      Read_Pointer <= Read_Pointer + 1;
      Read_Pointer_Gray <= bin2gray(Read_Pointer + 1);
    end
  end
  
  // Synchronize write pointer to read clock domain
  always @(posedge RClk) begin
    if (RReset == 1'b1) begin
      Write_Pointer_Gray_Sync1 <= 0;
      Write_Pointer_Gray_Sync2 <= 0;
    end
    else begin
      Write_Pointer_Gray_Sync1 <= Write_Pointer_Gray;
      Write_Pointer_Gray_Sync2 <= Write_Pointer_Gray_Sync1;
    end
  end
  
  // Full and Empty flags
  assign Full = (Write_Pointer_Gray == {~Read_Pointer_Gray_Sync2[4:3], 
                                         Read_Pointer_Gray_Sync2[2:0]});
  
  assign Empty = (Read_Pointer_Gray == Write_Pointer_Gray_Sync2);

endmodule

//===========================================
// INTERFACE
//===========================================

interface ASYNC_FIFO_if;
  
  logic WClk, RClk;
  logic Write, Read;
  logic Full, Empty;
  logic [7:0] Data_in;
  logic [7:0] Data_out;
  logic WReset, RReset;
  
endinterface
