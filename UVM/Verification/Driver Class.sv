class uart_driver extends uvm_driver #(uart_sequence_item);
  `uvm_component_utils(uart_driver)

  virtual uart_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
    uart_sequence_item req;
    forever begin
      seq_item_port.get_next_item(req);

      vif.tx_data   = req.tx_data;
      vif.length    = req.length;
      vif.parity_en = req.parity_en;
      vif.parity_type = req.parity_type;
      vif.stop2     = req.stop2;
      vif.baud      = req.baud;

      vif.tx_start  = 1;
      @(posedge vif.clk);
      vif.tx_start  = 0;

      seq_item_port.item_done();
    end
  endtask
endclass
