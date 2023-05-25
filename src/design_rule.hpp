#define FMT_HEADER_ONLYget_n
#include <fmt/core.h>
#include <fmt/format.h>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <vector>

class DesignRuleWriter {
public:
  // step 6
  void write_geometric_variables();
  void write_geometric_variables_left_tip_helper();
  void write_geometric_variables_right_tip_helper();
  void write_geometric_variables_front_tip_helper();
  void write_geometric_variables_back_tip_helper();

  // step 7
  void write_MAR_rule(int mar_Parameter, int doublePowerRail);

  // step 8
  void write_EOL_rule(int EOL_Parameter, int doublePowerRail);
  void write_EOL_RL_tip_helper(int EOL_Parameter);
  void write_EOL_LR_tip_helper(int EOL_Parameter);
  void write_EOL_BF_tip_helper(int EOL_Parameter, int doublePowerRail);
  void write_EOL_FB_tip_helper(int EOL_Parameter, int doublePowerRail);

  // step 9
  void write_VR_rule(float VR_Parameter, int doublePowerRail);
  void write_VR_M1_helper(float VR_Parameter, int doublePowerRail);
  void write_VR_M2_M4_helper(float VR_Parameter, int doublePowerRail);

  // step 10
  void write_PRL_rule(int PRL_Parameter, int doublePowerRail);
  void write_PRL_LR_tip_helper(int PRL_Parameter);
  void write_PRL_RL_tip_helper(int PRL_Parameter);
  void write_PRL_FB_tip_helper(int PRL_Parameter, int doublePowerRail);
  void write_PRL_BF_tip_helper(int PRL_Parameter, int doublePowerRail);

  // step 12
  void write_pin_access_rule(int MPL_Parameter, int MAR_Parameter, int EOL_Parameter);
  void write_pin_access_rule_helper(int MPL_Parameter, int MAR_Parameter,
                                        int EOL_Parameter);
  void write_pin_access_rule_via_enclosure_helper();
  void write_pin_access_rule_via23_helper();
  void write_pin_access_rule_via34_helper();

  // step 13
  void write_SHR_rule(int SHR_Parameter);
  void write_SHR_L_tip_helper(int SHR_Parameter);
  void write_SHR_R_tip_helper(int SHR_Parameter);
  void write_SHR_F_tip_helper(int SHR_Parameter);
  void write_SHR_B_tip_helper(int SHR_Parameter);
};