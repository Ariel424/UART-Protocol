class uart_monitor extends uvm_monitor;
  `uvm_component_utils(uart_monitor)

  virtual uart_if vif;
  uvm_analysis_port #(uart_sequence_item) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    if(!uvm_config_db#(virtual uart_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
    uart_sequence_item tr;

    forever begin
      @(posedge vif.rx_done);

      tr = uart_sequence_item::type_id::create("tr");
      tr.tx_data = vif.rx_out;

      mon_ap.write(tr);
    end
  endtask
endclass
