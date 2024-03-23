`timescale 1ns/10ps

/* verilator lint_off EOFNEWLINE */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off UNUSEDSIGNAL */
module tb_triggering #(
        parameter longint unsigned MAX_CYCLES = 100000000
      , parameter WAVE_ENABLE = 0
    ) ();

  // Define input/output variables
  reg clk; 
  reg rst_n;
  reg walk; 
  wire [1:0] signal, signal_golden; 
  wire signal_diff;

  // Generate clock and reset
  localparam int unsigned CLOCK_PERIOD = 10ns;
  longint unsigned cycles;
  initial begin
    $display("\nINFO: Starting simulation with bug triggering inputs\n");
    clk = 1'b0;
    rst_n = 1'b0;
    repeat(8)
      #(CLOCK_PERIOD/2) clk = ~clk;
    rst_n = 1'b1;
    cycles = 0; 
    forever begin
      #(CLOCK_PERIOD/2) clk = 1'b1;
      #(CLOCK_PERIOD/2) clk = 1'b0;

      if (cycles >= MAX_CYCLES) begin 
          $display("\nINFO: Max cycles reached %d\n\n", MAX_CYCLES);
          $finish(); 
      end
      cycles++;
    end
  end


  // Generate testing inputs
  reg test_rst_n; 
  initial begin
    // initialize variables
    walk = 1'b0; 
    test_rst_n = 1'b1; 
    
    wait(~rst_n); // wait for reset
    wait(rst_n); // wait for reset
        
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b1; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); walk = 1'b0; 
    @(negedge clk); 
    @(negedge clk); 
    @(negedge clk); 
    $finish(); 
  end

  // Print statements for analysis
  // Function to return state name based on state value
  localparam RED = 0;
  localparam GREEN = 1;
  localparam YELLOW = 2;
  function string getStateName(input [1:0] state_value);
    case(state_value)
      RED: getStateName = "RED";
      GREEN: getStateName = "GREEN";
      YELLOW: getStateName = "YELLOW";
      default: getStateName = "UNKNOWN_STATE";
    endcase
  endfunction
  //initial begin
  always @(posedge clk) begin
    if (!rst_n) begin ; end
    else begin
      $display("time=%4d, walk=%h, signal=%6s, signal_golden=%6s, signal_diff=%h"
              , $time, walk, getStateName(signal), getStateName(signal_golden), signal_diff); 
    end
  end

  // Dump waveforms
  initial begin
    if (WAVE_ENABLE == 1) begin
      $display("\nINFO: Dumping waveform\n");
      //$vcdpluson;
      //$dumpfile("testttt.vcd");
      //$dumpon; 
    end
  end


  //// Assertions
  //assert property (@(posedge clk) disable iff ((!rst_n)) 
  //                  (signal == RED) |-> ($past(signal) == YELLOW) || ($past(signal) == RED))
  //    else $display("ERROR, Yellow signal skipped!!, time=%4d, signal=%6s, past_signa=%6s"
  //            , $time, getStateName(signal), getStateName($past(signal))); 


  //// Initiate module
  traffic_controller #(
  ) tc_u (
      .clk      (clk)
    , .rst_ni   (!(!rst_n || !test_rst_n))
    , .walk_i   (walk)
    , .signal_o (signal)  
  ); 

  traffic_controller_golden #(
  ) tc_golden_u (
      .clk      (clk)
    , .rst_ni   (!(!rst_n || !test_rst_n))
    , .walk_i   (walk)
    , .signal_o (signal_golden)  
  ); 

  assign signal_diff = (signal != signal_golden); 

endmodule


