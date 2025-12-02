`include "uvm_macros.svh"
import uvm_pkg::*;

//////////////////////////////////////////////////////////////
//                      CONFIGURATION
//////////////////////////////////////////////////////////////

class uart_config extends uvm_object;
  `uvm_object_utils(uart_config)

  uvm_active_passive_enum is_active = UVM_ACTIVE;

  function new(string name = "uart_config");
    super.new(name);
  endfunction
endclass


//////////////////////////////////////////////////////////////
//                     ENUM DECLARATION
//////////////////////////////////////////////////////////////

typedef enum bit [3:0] {
  rand_baud_1_stop   = 0,
  rand_length_1_stop = 1,
  length5wp          = 2,
  length6wp          = 3,
  length7wp          = 4,
  length8wp          = 5,
  length5wop         = 6,
  length6wop         = 7,
  length7wop         = 8,
  length8wop         = 9,
  rand_baud_2_stop   = 11,
  rand_length_2_stop = 12
} oper_mode;


//////////////////////////////////////////////////////////////
//                    TRANSACTION CLASS
//////////////////////////////////////////////////////////////

class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)

  // Randomizable fields
  rand oper_mode   op;
  rand logic [7:0] tx_data;
  rand logic [16:0] baud;
  rand logic [3:0]  length;
  rand logic        parity_type;
  rand logic        parity_en;

  // Non-random fields
  logic tx_start, rx_start;
  logic rst;
  logic stop2;
  logic tx_done, rx_done;
  logic tx_err,  rx_err;
  logic [7:0] rx_out;

  // Constraints
  constraint baud_c   { baud inside {4800, 9600, 14400, 19200, 38400, 57600}; }
  constraint length_c { length inside {5, 6, 7, 8}; }

  function new(string name = "transaction");
    super.new(name);
  endfunction
endclass


//////////////////////////////////////////////////////////////
//                 RANDOM SEQUENCES (MULTIPLE)
//////////////////////////////////////////////////////////////

// Random baud, fixed length = 8, parity enabled, 1 stop
class rand_baud extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud)

  transaction tr;

  function new(string name = "rand_baud");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = rand_baud_1_stop;
      tr.length    = 8;
      tr.baud      = 9600;
      tr.rst       = 1'b0;
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


// Random baud, fixed length = 8, parity enabled, 2 stop bits
class rand_baud_with_stop extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_with_stop)

  transaction tr;

  function new(string name = "rand_baud_with_stop");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = rand_baud_2_stop;
      tr.length    = 8;
      tr.rst       = 1'b0;
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b1;

      finish_item(tr);
    end
  endtask
endclass


//////////////////////////////////////////////////////////////
//       FIXED LENGTH WITH PARITY (5, 6, 7, 8 BITS)
//////////////////////////////////////////////////////////////

class rand_baud_len5p extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len5p)

  transaction tr;

  function new(string name = "rand_baud_len5p");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length5wp;
      tr.rst       = 1'b0;
      tr.length    = 5;
      tr.tx_data   = {3'b000, tr.tx_data[7:3]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len6p extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len6p)

  transaction tr;

  function new(string name = "rand_baud_len6p");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length6wp;
      tr.rst       = 1'b0;
      tr.length    = 6;
      tr.tx_data   = {2'b00, tr.tx_data[7:2]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len7p extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len7p)

  transaction tr;

  function new(string name = "rand_baud_len7p");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length7wp;
      tr.rst       = 1'b0;
      tr.length    = 7;
      tr.tx_data   = {1'b0, tr.tx_data[7:1]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len8p extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len8p)

  transaction tr;

  function new(string name = "rand_baud_len8p");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length8wp;
      tr.rst       = 1'b0;
      tr.length    = 8;
      tr.tx_data   = tr.tx_data;
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b1;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


//////////////////////////////////////////////////////////////
//         FIXED LENGTH WITHOUT PARITY (5,6,7,8 BITS)
//////////////////////////////////////////////////////////////

class rand_baud_len5 extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len5)

  transaction tr;

  function new(string name = "rand_baud_len5");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length5wop;
      tr.rst       = 1'b0;
      tr.length    = 5;
      tr.tx_data   = {3'b000, tr.tx_data[7:3]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b0;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len6 extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len6)

  transaction tr;

  function new(string name = "rand_baud_len6");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length6wop;
      tr.rst       = 1'b0;
      tr.length    = 6;
      tr.tx_data   = {2'b00, tr.tx_data[7:2]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b0;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len7 extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len7)

  transaction tr;

  function new(string name = "rand_baud_len7");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length7wop;
      tr.rst       = 1'b0;
      tr.length    = 7;
      tr.tx_data   = {1'b0, tr.tx_data[7:1]};
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b0;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


class rand_baud_len8 extends uvm_sequence #(transaction);
  `uvm_object_utils(rand_baud_len8)

  transaction tr;

  function new(string name = "rand_baud_len8");
    super.new(name);
  endfunction

  virtual task body();
    repeat (5) begin
      tr = transaction::type_id::create("tr");
      start_item(tr);
      assert(tr.randomize);

      tr.op        = length8wop;
      tr.rst       = 1'b0;
      tr.length    = 8;
      tr.tx_data   = tr.tx_data;
      tr.tx_start  = 1'b1;
      tr.rx_start  = 1'b1;
      tr.parity_en = 1'b0;
      tr.stop2     = 1'b0;

      finish_item(tr);
    end
  endtask
endclass


//////////////////////////////////////////////////////////////
//                        DRIVER
//////////////////////////////////////////////////////////////

class driver extends uvm_driver #(transaction);
  `uvm_component_utils(driver)

  virtual uart_if vif;
  transaction tr;

  function new(string path = "drv", uvm_component parent = null);
    super.new(path, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    tr = transaction::type_id::create("tr");

    if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_error("DRV", "Unable to access Interface");
  endfunction


  // Reset logic
  task reset_dut();
    repeat (5) begin
      vif.rst         <= 1'b1;
      vif.tx_start    <= 1'b0;
      vif.rx_start    <= 1'b0;
      vif.tx_data     <= 8'h00;
      vif.baud        <= 16'h0;
      vif.length      <= 4'h0;
      vif.parity_type <= 1'b0;
      vif.parity_en   <= 1'b0;
      vif.stop2       <= 1'b0;

      `uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM);
      @(posedge vif.clk);
    end
  endtask


  // Main drive loop
  task drive();
    reset_dut();

    forever begin
      seq_item_port.get_next_item(tr);

      vif.rst         <= 1'b0;
      vif.tx_start    <= tr.tx_start;
      vif.rx_start    <= tr.rx_start;
      vif.tx_data     <= tr.tx_data;
      vif.baud        <= tr.baud;
      vif.length      <= tr.length;
      vif.parity_type <= tr.parity_type;
      vif.parity_en   <= tr.parity_en;
      vif.stop2       <= tr.stop2;

      `uvm_info("DRV",
        $sformatf("BAUD:%0d LEN:%0d PAR_T:%0d PAR_EN:%0d STOP:%0d TX_DATA:%0d",
          tr.baud, tr.length, tr.parity_type, tr.parity_en, tr.stop2, tr.tx_data),
        UVM_NONE
      );

      @(posedge vif.clk);
      @(posedge vif.tx_done);
      @(negedge vif.rx_done);

      seq_item_port.item_done();
    end
  endtask


  virtual task run_phase(uvm_phase phase);
    drive();
  endtask
endclass


//////////////////////////////////////////////////////////////
//                        MONITOR
//////////////////////////////////////////////////////////////

class mon extends uvm_monitor;
  `uvm_component_utils(mon)

  uvm_analysis_port #(transaction) send;
  transaction tr;
  virtual uart_if vif;

  function new(string inst = "mon", uvm_component parent = null);
    super.new(inst, parent);
  endfunction


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    tr   = transaction::type_id::create("tr");
    send = new("send", this);

    if (!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_error("MON", "Unable to access Interface");
  endfunction


  virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);

      if (vif.rst) begin
        tr.rst = 1'b1;
        `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
        send.write(tr);
      end

      else begin
        @(posedge vif.tx_done);

        tr.rst         = 1'b0;
        tr.tx_start    = vif.tx_start;
        tr.rx_start    = vif.rx_start;
        tr.tx_data     = vif.tx_data;
        tr.baud        = vif.baud;
        tr.length      = vif.length;
        tr.parity_type = vif.parity_type;
        tr.parity_en   = vif.parity_en;
        tr.stop2       = vif.stop2;

        @(negedge vif.rx_done);
        tr.rx_out = vif.rx_out;

        `uvm_info("MON",
          $sformatf("BAUD:%0d LEN:%0d PAR_T:%0d PAR_EN:%0d STOP:%0d TX_DATA:%0d RX_DATA:%0d",
            tr.baud, tr.length, tr.parity_type, tr.parity_en,
            tr.stop2, tr.tx_data, tr.rx_out),
          UVM_NONE
        );

        send.write(tr);
      end
    end
  endtask

endclass
