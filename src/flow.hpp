#define FMT_HEADER_ONLYget_n
#include <fmt/core.h>
#include <fmt/format.h>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <regex>

class FlowWriter {
public:
  void init_commodity_flow_var();

  void localize_commodity(int local_Parameter, int tolerance_Parameter);

  void localize_commodity_helper(int col, int commodityIndex, int netIndex, bool DEBUG);

  // Flow Capacity Control
  void write_flow_capacity_control();

  // Part 1
  void write_flow_conservation(FILE *fp, int EXT_Parameter);

  // Part 2
  void write_vertex_exclusive(FILE *fp);

  // Part 3
  void write_edge_assignment(FILE *fp);

  // Part 4
  void write_edge_exclusive(FILE *fp);

  // Part 11
  void write_net_consistency();
};