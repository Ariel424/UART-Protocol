class uart_test extends uvm_test;
  `uvm_component_utils(uart_test)

  uart_env env;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    env = uart_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    uart_random_seq seq = uart_random_seq::type_id::create("seq");
    phase.raise_objection(this);
      seq.start(env.agent.sequencer);
    phase.drop_objection(this);
  endtask
endclass
