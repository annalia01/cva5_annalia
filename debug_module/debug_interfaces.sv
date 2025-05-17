typedef struct packed {
    logic [6:0] address;
    logic [31:0] jtag_data;
    logic new_request;
    logic rnw;
} jtag_dmi_interface_output;

typedef struct packed {
    logic handled;
    logic [1:0] response;
    logic [31:0] dmi_data;
} jtag_dmi_interface_input;

typedef struct packed {
    logic handled;
    logic [1:0] response;
    logic [31:0] dmi_data;
} dmi_dmi_interface_output;

typedef struct packed {
    logic [6:0] address;
    logic [31:0] jtag_data;
    logic new_request;
    logic rnw;
} dmi_dmi_interface_input;

typedef struct packed {
    logic halt;
    logic resume;
    logic reset;
    logic [31:0] write_data;
    logic [31:0] read_write_addr;
    logic rnw;
    logic rnw_new_request;
    logic [31:0] program_buffer_data;
} dmi_dmi_cpu_interface_output;

typedef struct packed {
    logic halt_ack;
    logic resume_ack;
    logic reset_ack;
    logic halt_ack_recv;
    logic resume_ack_recv;
    logic running;
    logic [31:0] read_data;
    logic rnw_ack;
    logic [3:0] program_buffer_addr;
} dmi_dmi_cpu_interface_input;

typedef struct packed {
    logic halt_ack;
    logic resume_ack;
    logic reset_ack;
    logic halt_ack_recv;
    logic resume_ack_recv;
    logic running;
    logic [31:0] read_data;
    logic rnw_ack;
    logic [3:0] program_buffer_addr;
} cpu_dmi_cpu_interface_output;

typedef struct packed {
    logic halt;
    logic resume;
    logic reset;
    logic [31:0] write_data;
    logic [31:0] read_write_addr;
    logic rnw;
    logic rnw_new_request;
    logic [31:0] program_buffer_data;
} cpu_dmi_cpu_interface_input;
