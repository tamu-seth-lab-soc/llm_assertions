`timescale 1ns/10ps

/* verilator lint_off EOFNEWLINE */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off UNUSEDSIGNAL */
module traffic_controller_golden (
    input clk, 
    input rst_ni,
    input walk_i, 
    output reg [1:0] signal_o 
  ); 

  localparam RED = 0;
  localparam GREEN = 1;
  localparam YELLOW = 2;
  localparam WALK_TIME = 4; // red for 4 clock cycles for pedestrians to cross

  reg [1:0] walk_ctr; 


  // red - yellow - green control FSM
  always @ (posedge clk) begin
    if (!rst_ni) begin
      signal_o <= #1 RED; 
    end
    else begin
      case (signal_o)
        RED: begin
          if (walk_i) begin
            signal_o <= #1 RED; 
          end
          else if (walk_ctr != 'b0) begin
            signal_o <= #1 RED; 
          end
          else
            signal_o <= #1 GREEN; 
        end
        GREEN: begin
          signal_o <= #1 YELLOW; 
        end
        YELLOW: begin
          signal_o <= #1 RED; 
        end
        default: 
          signal_o <= #1 RED; 
      endcase
    end
  end

  // walk counter
  always @ (posedge clk) begin
    if (!rst_ni) begin
      walk_ctr <=  #1 'b0;  
    end
    else begin
      if (walk_i) begin
        walk_ctr <= #1 WALK_TIME-1; 
      end
      else if (signal_o == RED) begin
        walk_ctr <= #1 (walk_ctr == 'b0) ? 'b0 : walk_ctr - 1; 
      end
    end
  end


endmodule

