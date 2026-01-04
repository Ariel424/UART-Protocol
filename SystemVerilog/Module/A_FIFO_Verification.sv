// Transaction Class
class FIFO_transaction;
  rand bit [7:0] data;
  rand bit write;
  rand bit read;
  
  constraint c_write_read {
    write dist {1 := 70, 0 := 30};
    read dist {1 := 70, 0 := 30};
  }
  
  function void display(string tag = "");
    $display("[%0t] %s Write=%0b Read=%0b Data=0x%0h", 
             $time, tag, write, read, data);
  endfunction
endclass

// Driver Class
class FIFO_driver;
  virtual ASYNC_FIFO_if vif;
  mailbox #(FIFO_transaction) mbx;
  
  function new(mailbox #(FIFO_transaction) mbx, virtual ASYNC_FIFO_if vif);
    this.mbx = mbx;
    this.vif = vif;
  endfunction
  
  task run();
    FIFO_transaction txn;
    forever begin
      mbx.get(txn);
      @(posedge vif.WClk);
      vif.Write = txn.write;
      vif.Data_in = txn.data;
      @(posedge vif.RClk);
      vif.Read = txn.read;
      txn.display("DRIVER");
    end
  endtask
endclass

// Monitor Class
class FIFO_monitor;
  virtual ASYNC_FIFO_if vif;
  mailbox #(FIFO_transaction) mbx_write;
  mailbox #(FIFO_transaction) mbx_read;
  
  function new(virtual ASYNC_FIFO_if vif);
    this.vif = vif;
    mbx_write = new();
    mbx_read = new();
  endfunction
  
  task run();
    fork
      monitor_write();
      monitor_read();
    join
  endtask
  
  task monitor_write();
    FIFO_transaction txn;
    forever begin
      @(posedge vif.WClk);
      if (vif.Write && !vif.Full) begin
        txn = new();
        txn.data = vif.Data_in;
        txn.write = 1;
        mbx_write.put(txn);
        $display("[%0t] MONITOR_WRITE: Data=0x%0h", $time, txn.data);
      end
    end
  endtask
  
  task monitor_read();
    FIFO_transaction txn;
    forever begin
      @(posedge vif.RClk);
      if (vif.Read && !vif.Empty) begin
        @(posedge vif.RClk); // Wait for output
        txn = new();
        txn.data = vif.Data_out;
        txn.read = 1;
        mbx_read.put(txn);
        $display("[%0t] MONITOR_READ: Data=0x%0h", $time, txn.data);
      end
    end
  endtask
endclass

// Scoreboard Class
class FIFO_scoreboard;
  mailbox #(FIFO_transaction) mbx_write;
  mailbox #(FIFO_transaction) mbx_read;
  FIFO_transaction write_queue[$];
  int match_count = 0;
  int mismatch_count = 0;
  
  function new(mailbox #(FIFO_transaction) mbx_w, mailbox #(FIFO_transaction) mbx_r);
    this.mbx_write = mbx_w;
    this.mbx_read = mbx_r;
  endfunction
  
  task run();
    fork
      collect_write();
      check_read();
    join
  endtask
  
  task collect_write();
    FIFO_transaction txn;
    forever begin
      mbx_write.get(txn);
      write_queue.push_back(txn);
    end
  endtask
  
  task check_read();
    FIFO_transaction txn_read, txn_expected;
    forever begin
      mbx_read.get(txn_read);
      if (write_queue.size() > 0) begin
        txn_expected = write_queue.pop_front();
        if (txn_read.data == txn_expected.data) begin
          match_count++;
          $display("[%0t] SCOREBOARD MATCH: Expected=0x%0h Got=0x%0h", 
                   $time, txn_expected.data, txn_read.data);
        end else begin
          mismatch_count++;
          $display("[%0t] SCOREBOARD MISMATCH: Expected=0x%0h Got=0x%0h", 
                   $time, txn_expected.data, txn_read.data);
        end
      end else begin
        $display("[%0t] SCOREBOARD ERROR: Read from empty FIFO", $time);
        mismatch_count++;
      end
    end
  endtask
  
  function void report();
    $display("\n===== SCOREBOARD REPORT =====");
    $display("Matches: %0d", match_count);
    $display("Mismatches: %0d", mismatch_count);
    $display("Remaining in queue: %0d", write_queue.size());
    if (mismatch_count == 0)
      $display("TEST PASSED");
    else
      $display("TEST FAILED");
    $display("=============================\n");
  endfunction
endclass

// Environment Class
class FIFO_environment;
  FIFO_driver drv;
  FIFO_monitor mon;
  FIFO_scoreboard scb;
  mailbox #(FIFO_transaction) mbx_drv;
  virtual ASYNC_FIFO_if vif;
  
  function new(virtual ASYNC_FIFO_if vif);
    this.vif = vif;
    mbx_drv = new();
    mon = new(vif);
    scb = new(mon.mbx_write, mon.mbx_read);
    drv = new(mbx_drv, vif);
  endfunction
  
  task run(int num_txns);
    fork
      drv.run();
      mon.run();
      scb.run();
    join_none
    
    // Generate and send transactions
    repeat(num_txns) begin
      FIFO_transaction txn = new();
      assert(txn.randomize());
      mbx_drv.put(txn);
    end
    
    // Wait for operations to complete
    #10000;
  endtask
endclass

// Testbench Module
module tb_async_fifo;
  // Clock generation
  bit WClk = 0, RClk = 0;
  always #5 WClk = ~WClk;  // 100MHz
  always #7 RClk = ~RClk;  // ~71MHz (different frequency)
  
  // Interface instantiation
  ASYNC_FIFO_if fifo_if();
  
  // DUT instantiation
  ASYNC_FIFO dut (
    .WClk(fifo_if.WClk),
    .WReset(fifo_if.WReset),
    .Write(fifo_if.Write),
    .Din(fifo_if.Data_in),
    .Full(fifo_if.Full),
    .RClk(fifo_if.RClk),
    .RReset(fifo_if.RReset),
    .Read(fifo_if.Read),
    .Dout(fifo_if.Data_out),
    .Empty(fifo_if.Empty)
  );
  
  // Connect clocks
  assign fifo_if.WClk = WClk;
  assign fifo_if.RClk = RClk;
  
  // Coverage
  covergroup fifo_cg @(posedge WClk);
    cp_write: coverpoint fifo_if.Write {
      bins write_0 = {0};
      bins write_1 = {1};
    }
    cp_full: coverpoint fifo_if.Full {
      bins full_0 = {0};
      bins full_1 = {1};
    }
    cp_data: coverpoint fifo_if.Data_in {
      bins low = {[0:63]};
      bins mid = {[64:191]};
      bins high = {[192:255]};
    }
    cross_write_full: cross cp_write, cp_full;
  endgroup
  
  covergroup fifo_read_cg @(posedge RClk);
    cp_read: coverpoint fifo_if.Read {
      bins read_0 = {0};
      bins read_1 = {1};
    }
    cp_empty: coverpoint fifo_if.Empty {
      bins empty_0 = {0};
      bins empty_1 = {1};
    }
    cross_read_empty: cross cp_read, cp_empty;
  endgroup
  
  // Assertions
  property p_no_write_when_full;
    @(posedge WClk) (fifo_if.Full && fifo_if.Write) |=> $stable(fifo_if.Full);
  endproperty
  
  property p_no_read_when_empty;
    @(posedge RClk) (fifo_if.Empty && fifo_if.Read) |=> $stable(fifo_if.Empty);
  endproperty
  
  assert_no_write_full: assert property(p_no_write_when_full)
    else $error("Write occurred when FIFO was full");
  
  assert_no_read_empty: assert property(p_no_read_when_empty)
    else $error("Read occurred when FIFO was empty");
  
  // Test execution
  initial begin
    FIFO_environment env;
    fifo_cg fcg = new();
    fifo_read_cg frcg = new();
    
    // Initialize
    fifo_if.Write = 0;
    fifo_if.Read = 0;
    fifo_if.Data_in = 0;
    fifo_if.WReset = 1;
    fifo_if.RReset = 1;
    
    repeat(10) @(posedge WClk);
    fifo_if.WReset = 0;
    fifo_if.RReset = 0;
    repeat(10) @(posedge WClk);
    
    // Run test
    env = new(fifo_if);
    $display("Starting FIFO Verification...");
    env.run(200);
    
    // Report results
    repeat(100) @(posedge WClk);
    env.scb.report();
    $display("Write Coverage: %.2f%%", fcg.get_coverage());
    $display("Read Coverage: %.2f%%", frcg.get_coverage());
    
    $finish;
  end
  
  // Waveform dump
  initial begin
    $dumpfile("fifo.vcd");
    $dumpvars(0, tb_async_fifo);
  end
endmodule
