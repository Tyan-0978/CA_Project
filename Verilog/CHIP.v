// Your code
module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    // TODO: add opcode parameters
    // required: 
    // - auipc, jal, jalr, beq, lw, sw
    // - addi, slti, add, sub, xor, mul
    // bonus:
    // - ...

    parameter AUIPC = 7'b0010111;
    parameter JAL = 7'b1101111;
    parameter JALR = 7'b1100111;
    parameter BEQ = 7'b1100011;
    parameter LW = 7'b0000011;
    parameter SW = 7'b0100011;

    // use Imm
    // parameter ADDI = 7'b0010011;
    // parameter SLTI = 7'b0010011;
    parameter IMM = 7'b0010011;

    //  calc
    // parameter ADD = 7'b0110011;
    // parameter SUB = 7'b0110011;
    // parameter XOR = 7'b0110011;
    // parameter MUL = 7'b0110011;
    parameter MATH = 7'b0110011;


    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg    [31:0] PC_nxt      ;              //
    reg           regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg    [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg
    // for instruction decoding
    wire [6:0] opcode;
    // wire [4:0] decode_rd;
    wire [2:0] funct3;
    // wire [4:0] decode_rs1;
    // wire [4:0] decode_rs2;
    wire [6:0] funct7;
    // Imm
    wire signed[20:0] jal_imm;
    wire [31:0] auipc_imm;
    wire signed[12:0] beq_imm;
    wire signed[11:0] jalr_imm;
    wire [11:0] sw_imm;

    //----------------------//
    wire [1:0] mode;        //
    wire valid;             //
    wire ready;             //
    wire [63:0] mul_out;    //
    //----------------------//

    // state for mul operation FSM
    // state 0 for general case, 1 for mulDiv
    reg isMUL, next_isMUL;

    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//
    //---------------------------------------//
    mulDiv reg1(                             //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .valid(valid),                       //
        .ready(ready),                       //
        .mode(mode),                         //
        .in_A(rs1_data),                     //
        .in_B(rs2_data),                     //
        .out(mul_out));                      //
    //---------------------------------------//


    // Todo: any combinational/sequential circuit

    // wire assignments
    assign opcode = mem_rdata_I[6:0];
    assign rd     = mem_rdata_I[11:7];
    assign funct3 = mem_rdata_I[14:12];
    assign rs1    = mem_rdata_I[19:15];
    assign rs2    = mem_rdata_I[24:20];
    assign funct7 = mem_rdata_I[31:25];

    // ============= Imm ============
    // jal
    assign jal_imm[20] = mem_rdata_I[31];
    assign jal_imm[10:1] = mem_rdata_I[30:21];
    assign jal_imm[11] = mem_rdata_I[20];
    assign jal_imm[19:12] = mem_rdata_I[19:12];
    assign jal_imm[0] = 0;
    // auipc
    assign auipc_imm[31:12] = mem_rdata_I[31:12];
    assign auipc_imm[11:0] = 12'd0;
    // beq
    assign beq_imm[12] = mem_rdata_I[31];
    assign beq_imm[11] = mem_rdata_I[7];
    assign beq_imm[10:5] = mem_rdata_I[30:25];
    assign beq_imm[4:1] = mem_rdata_I[11:8];
    assign beq_imm[0] = mem_rdata_I[0];
    // sw
    assign sw_imm[11:5] = mem_rdata_I[31:25];
    assign sw_imm[4:0] = mem_rdata_I[11:7];

    assign jalr_imm = mem_rdata_I[31:20];
    // ===============================

    // ============= OUTPUT ============

    reg [31:0] Addr_Data;
    assign mem_wen_D = (opcode == SW)? 1 : 0;
    assign mem_addr_D = Addr_Data;
    assign mem_wdata_D = (opcode == SW)? rs2_data : 32'd0;
    assign mem_addr_I = PC;


    // ============= MUL ============
    assign valid = ((opcode == MATH && funct3==3'b000) && funct7==7'd1)? 1:0;
    assign mode = 2'b01;


    //============================================
    //==========  combinational part  ============
    //============================================

    always @(*) begin

    // mem_addr_D
    case(opcode)
        LW: Addr_Data = rs1_data + mem_rdata_I[31:20];
        SW: Addr_Data = rs1_data + sw_imm;
        default: Addr_Data = 0;
    endcase
    // only for rd_data
	case(opcode)

        AUIPC:begin
            rd_data = PC + auipc_imm;
        end

        JAL:begin
            rd_data = PC + 32'd4;
        end

        JALR:begin
            rd_data = PC + 32'd4;
        end

        // BEQ:begin
        // end

        LW:begin
            rd_data = mem_rdata_D;
        end

        // SW:begin
        // end

        IMM:begin
            if(funct3 == 3'b000) begin
                rd_data = rs1_data + mem_rdata_I[31:20];
            end
            else begin
                if(rs1_data < mem_rdata_I[31:20]) rd_data = 32'd1;
                else rd_data = 32'd0;
            end
        end

        MATH:begin
            case(funct3)
                3'b000:begin
                    case(funct7)
                        // ADD
                        7'b0000000: rd_data = rs1_data + rs2_data;
                        // SUB
                        7'b0100000: rd_data = rs1_data - rs2_data;
                        // MUL
                        7'b0000001: rd_data = mul_out[31:0];
                        default: rd_data = 32'd0;
                    endcase
                end

                3'b100:begin
                    rd_data = rs1_data ^ rs2_data;
                end

                default:begin
                    rd_data = 32'd0;
                end
            endcase
        end

	    default:begin
            rd_data = 32'd0;
        end
	endcase

    // only for PC_nxt
    case(opcode)
        JAL:    PC_nxt = PC + jal_imm;
        JALR:   PC_nxt = rs1_data + jalr_imm;
        BEQ:    PC_nxt = PC + beq_imm;
        //  MUL
        MATH: begin
            if (funct3 == 3'b000 && funct7 == 7'b0000001) begin
                if(ready) PC_nxt = PC + 4;
                else PC_nxt = PC;
            end
            else begin
                PC_nxt = PC + 4;
            end
        end
        default: PC_nxt = PC + 4;
    endcase

    // regWrite
    case(opcode)
        SW: regWrite = 0;
        MATH: begin
            if (funct3 == 3'b000 && funct7 == 7'b0000001) begin
                if(ready) regWrite = 1;
                else regWrite = 0;
            end
            else begin
                regWrite = 1;
            end
        end
        default: regWrite = 1;
    endcase

    // State isMUL
    case(opcode)
        MATH: begin
            if (funct3 == 3'b000 && funct7 == 7'b0000001) begin
                if(ready) next_isMUL = 1;
                else next_isMUL = 0;
            end
            else begin
                next_isMUL = 0;
            end
        end
        default: next_isMUL = 0;
    endcase

    end

    //============================================
    //============  sequential part  =============
    //============================================

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            isMUL <= 0;
        end
        else begin
            PC <= PC_nxt;
            isMUL <= next_isMUL;
        end
    end
endmodule



module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2


    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: and, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter AND = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments

    assign out = (ready == 1) ? shreg : 0;
    assign ready = (state == OUT) ? 1 : 0;
    
    // Combinational always block
    // Todo 1: Next-state logic of state machine    Finished
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    case(mode)
                        0: state_nxt = MUL;
                        1: state_nxt = DIV;
                        2: state_nxt = AND;
                        3: state_nxt = AVG;
                        default: state_nxt = state;
                    endcase
                end
                else state_nxt = state;
            end

            MUL : begin
                if (counter == 31) state_nxt = OUT;
                else state_nxt = state;
            end

            DIV : begin
                if (counter == 31) state_nxt = OUT;
                else state_nxt = state;
            end

            AND : state_nxt = OUT;

            AVG : state_nxt = OUT;

            OUT : state_nxt = IDLE;

            default : state_nxt = state;
        endcase
    end

    // Todo 2: Counter
    
    always @(*) begin
        if(state == MUL || state == DIV) begin
            if(counter == 31) counter_nxt = 0;
            else counter_nxt = counter + 1;
        end
        else counter_nxt = 0;
    end
  

    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            IDLE: alu_out = 0;

            MUL : begin
                if (shreg[0]) alu_out = shreg[63:32] + alu_in;
                else alu_out = shreg[63:32];
            end

            DIV : begin
                alu_out = shreg[62:31] - alu_in;
            end

            AND : alu_out = alu_in & shreg[31:0];

            AVG : alu_out = alu_in + shreg[31:0];

            default: alu_out = alu_in;
        endcase
    end

    //MUL
    //|            33         | |       31        |

    // Todo 4: Shift register

    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) begin
                    shreg_nxt[31: 0] = in_A;
                    shreg_nxt[63:32] = 0;
                end
                else begin
                    shreg_nxt = shreg;
                end
            end

            MUL : begin
                shreg_nxt = shreg >> 1;
                shreg_nxt[63:31] = alu_out;
            end

            DIV : begin
                //  if negative, alu_out[32] must be 1
                if(alu_out[32]) begin
                    shreg_nxt = shreg << 1;
                end
                else begin
                    shreg_nxt = shreg << 1;
                    shreg_nxt[63:32] = alu_out;
                    shreg_nxt[0] = 1;
                end
            end

            AND : begin
                shreg_nxt[63:32] = 0;
                shreg_nxt[31:0] = alu_out;
            end

            AVG : begin
                shreg_nxt[63:32] = 0;
                shreg_nxt[31:0] = alu_out[32:1];
            end

            default: shreg_nxt = shreg;
        endcase
    end




    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            alu_in <= 0;
            shreg <= 0;
            counter <= 0;
        end
        else begin
            state <= state_nxt;
            alu_in <= alu_in_nxt;
            shreg <= shreg_nxt;
            counter <= counter_nxt;
        end
    end

endmodule
