class uart_scoreboard extends uvm_component;
  `uvm_component_utils(uart_scoreboard)

  uvm_analysis_imp #(uart_sequence_item, uart_scoreboard) sb_port;

  mailbox expected_mb = new();

  function new(string name, uvm_component parent);
    super.new(name, parent);
    sb_port = new("sb_port", this);
  endfunction

  function void write(uart_sequence_item tr);
    uart_sequence_item exp;
    expected_mb.get(exp);

    if(tr.tx_data !== exp.tx_data)
      `uvm_error("UART_SB", $sformatf("Mismatch: exp=%h got=%h",
                                      exp.tx_data, tr.tx_data));
    else
      `uvm_info("UART_SB", "UART transfer OK", UVM_LOW);
  endfunction
endclass
