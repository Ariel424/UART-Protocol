class uart_env extends uvm_env;
  `uvm_component_utils(uart_env)

  uart_agent      agent;
  uart_scoreboard sb;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    agent = uart_agent::type_id::create("agent", this);
    sb    = uart_scoreboard::type_id::create("sb", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    agent.monitor.mon_ap.connect(sb.sb_port);
  endfunction
endclass
