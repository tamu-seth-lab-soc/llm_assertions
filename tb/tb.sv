`timescale 1ns/10ps

/* verilator lint_off EOFNEWLINE */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off UNUSEDSIGNAL */
module tb #(
        parameter longint unsigned MAX_CYCLES = 100000000
      , parameter WAVE_ENABLE = 1
    ) ();

  // Define input/output variables
  reg clk; 
  reg rst_n;
  reg walk; 
  wire [1:0] signal, signal_buggy; 
  wire signal_diff;

  // Generate clock and reset
  localparam int unsigned CLOCK_PERIOD = 10ns;
  longint unsigned cycles;
  initial begin
    $display("\nINFO: Starting simulation\n");
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
  localparam NO_DUT_SIGNALS = 1; // 1 bit for walk
  localparam NO_CLOCKS = 15+1; // test traffic controller for different instances 
                             // over 15 clock cycles + 1 for reset
  localparam LOG2_NO_CLOCKS = 4; // base 2 log of NO_CLOCKS
  localparam CTR_WIDTH = (NO_DUT_SIGNALS*NO_CLOCKS) + LOG2_NO_CLOCKS; 
              // + LOG2_NO_CLOCKS to keep track of when to update counter
  
  reg [CTR_WIDTH-1:0] test_data; 
  wire test_data_curr; 
  wire test_rst_n; 
  always @(posedge clk) begin
      if (!rst_n) begin
          test_data <= 'b0; 
      end else begin
          if (test_data == {CTR_WIDTH{ 1'b1}}) begin // stop since all inputs are tested
              #(CLOCK_PERIOD/2) $display("Testing done, no inputs=%d", test_data+1); 
              #(CLOCK_PERIOD*2) $finish; 
          end else begin 
              #(CLOCK_PERIOD/2) test_data <= test_data + 1; 
          end 
      end
  end
  
  assign test_data_curr = test_data[test_data[LOG2_NO_CLOCKS-1:0]-1+LOG2_NO_CLOCKS]; 
 
  assign walk     = test_data_curr; 
  assign test_rst_n = !(test_data[LOG2_NO_CLOCKS-1:0] == 'b0);

  // Dump waveforms
  initial begin
    if (WAVE_ENABLE == 1) begin
      $display("\nINFO: Dumping waveform\n");
      $vcdpluson;
      //$dumpfile("testttt.vcd");
      //$dumpon; 
    end
  end


  //// Assertions
  //assert property (@(posedge clk) disable iff ((!rst_n)) (data[0]))
  //    else $display("ERROR, assertion violated, time=%4d, data=%h", $time, data); 

  
  //assert property (@(posedge clk)  (0))
  //    else $display("ERROR, assertion violated, time=%4d, data=%h", $time, data); 


  //// Initiate module
  traffic_controller #(
  ) tc_u (
      .clk      (clk)
    , .rst_ni   (!(!rst_n || !test_rst_n))
    , .walk_i   (walk)
    , .signal_o (signal)  
  ); 

  traffic_controller_buggy #(
  ) tc_buggy_u (
      .clk      (clk)
    , .rst_ni   (!(!rst_n || !test_rst_n))
    , .walk_i   (walk)
    , .signal_o (signal_buggy)  
  ); 

  assign signal_diff = (signal != signal_buggy); 

endmodule


