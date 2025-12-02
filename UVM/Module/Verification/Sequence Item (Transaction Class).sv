class uart_sequence_item extends uvm_sequence_item;
  rand bit [7:0] tx_data;
  rand bit [3:0] length;
  rand bit parity_type;
  rand bit parity_en;
  rand bit stop2;
  rand int unsigned baud;

  `uvm_object_utils(uart_sequence_item)

  function new(string name="uart_sequence_item");
    super.new(name);
  endfunction
endclass
