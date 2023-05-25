#include "flow.hpp"
#include "SMTCell.hpp"
#include "obj.hpp"

namespace bmp = boost::multiprecision;

/**
 * Localize commodity:
 * All connection between devices should be localized.
 * 
 * @param   local_Parameter        1: enable, 0: disable
 * @param   tolerance_Parameter    tolerance to connection boundary
 *
 * @return  void
 */
void FlowWriter::localize_commodity(int local_Parameter,
                                    int tolerance_Parameter) {
  if (local_Parameter == 1) {
    SMTCell::writeConstraint(";Localization.\n\n");
    SMTCell::writeConstraint(
        ";Conditional Localization for All Commodities\n\n");
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {

        // inst pin idx
        std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        if (pidx_s == Pin::keySON || pidx_t == Pin::keySON) {
          continue;
        }
        // pin ptr
        Pin *pin_s = SMTCell::getPin(pidx_s);
        Pin *pin_t = SMTCell::getPin(pidx_t);
        // external net should NOT be considered
        if (pin_s->getInstID() == "ext" || pin_t->getInstID() == "ext") {
          continue;
        }
        // inst idx
        int inst_pin_s = SMTCell::getPinInstIdx(pin_s);
        int inst_pin_t = SMTCell::getPinInstIdx(pin_t);
        // type
        std::string type_s = pin_s->getPinType();
        std::string type_t = pin_t->getPinType();
        // finger
        std::vector<int> finger_s = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(inst_pin_s)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        std::vector<int> finger_t = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(inst_pin_t)->getInstWidth(),
            SMTCell::getTrackEachPRow());

        // width
        int w_s = finger_s[0] * 2;
        int w_t = finger_t[0] * 2;
        int len = SMTCell::getBitLengthNumTrackV();

        int tmp_pidx_s = std::stoi(
            std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
        int tmp_pidx_t = std::stoi(
            std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));

        if (pidx_t != Pin::keySON) {
          // fmt::print("tmp_pidx_s: {}, tmp_pidx_t: {}\n", tmp_pidx_s,
          // tmp_pidx_t);
          for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
               col += SMTCell::getMetalOneStep()) {
            if (col % SMTCell::getMetalOneStep() != 0 &&
                col % SMTCell::getMetalThreeStep() != 0) {
              continue;
            }
            SMTCell::writeConstraint(fmt::format(
                "(assert (ite (and (= ff{} false) (= ff{} false)) (ite "
                "(bvsge (bvadd x{} (_ bv{} {})) (bvadd x{} (_ bv{} {})))\n",
                inst_pin_s, inst_pin_t, inst_pin_s,
                tmp_pidx_s * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV(), inst_pin_t,
                tmp_pidx_t * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            int tmp_col = (col - (tolerance_Parameter + tmp_pidx_s) *
                                     SMTCell::getMetalOneStep()) >= 0
                              ? (col - (tolerance_Parameter + tmp_pidx_s) *
                                           SMTCell::getMetalOneStep())
                              : (0);
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_col, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // # 1
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";1\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  true);

            SMTCell::writeConstraint(") (= true true))\n");
            int tmp_bv =
                ((col + (tolerance_Parameter - tmp_pidx_t) *
                            SMTCell::getMetalOneStep()) >=
                         (SMTCell::getRealNumTrackV() - 1)
                     ? (SMTCell::getRealNumTrackV() - 1)
                     : ((col + (tolerance_Parameter - tmp_pidx_t) *
                                   SMTCell::getMetalOneStep()) >= 0
                            ? (col + (tolerance_Parameter - tmp_pidx_t) *
                                         SMTCell::getMetalOneStep())
                            : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            // fmt::print(
            //     "1. bv:{}, col:{}, tolerance_Parameter:{}, tmp_pidx_t:{}\n",
            //     tmp_bv, col, tolerance_Parameter, tmp_pidx_t);

            // 2
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";2\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true)))\n");
            tmp_bv = (col - (tolerance_Parameter + tmp_pidx_t) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + tmp_pidx_t) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            // fmt::print("2. bv:{}\n", tmp_bv);

            // 3
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";3\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv = (col + (tolerance_Parameter - tmp_pidx_s) *
                                      SMTCell::getMetalOneStep() >=
                              SMTCell::getRealNumTrackV() - 1
                          ? (SMTCell::getRealNumTrackV() - 1)
                          : (col + (tolerance_Parameter - tmp_pidx_s) *
                                             SMTCell::getMetalOneStep() >=
                                     0
                                 ? (col + (tolerance_Parameter - tmp_pidx_s) *
                                              SMTCell::getMetalOneStep())
                                 : (0)));

            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            // fmt::print("3. bv:{}\n", tmp_bv);
            // 4
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";4\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))))\n");
            SMTCell::writeConstraint(fmt::format(
                "	(ite (and (= ff{} false) (= ff{} true)) (ite (bvsge "
                "(bvadd x{} (_ bv{} {})) (bvadd x{} (_ bv{} {})))\n",
                inst_pin_s, inst_pin_t, inst_pin_s,
                tmp_pidx_s * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV(), inst_pin_t,
                (w_t - tmp_pidx_t) * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            tmp_bv = (col - (tolerance_Parameter + tmp_pidx_s) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + tmp_pidx_s) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 5
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";5\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv =
                (col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                                 SMTCell::getMetalOneStep() >=
                         SMTCell::getRealNumTrackV() - 1
                     ? (SMTCell::getRealNumTrackV() - 1)
                     : (col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                                        SMTCell::getMetalOneStep() >=
                                0
                            ? (col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                                         SMTCell::getMetalOneStep())
                            : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 6
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";6\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true)))\n");
            tmp_bv = (col - (tolerance_Parameter + w_t - tmp_pidx_t) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + w_t - tmp_pidx_t) *
                                       SMTCell::getMetalOneStep())
                          : 0);
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 7
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";7\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv = (col + (tolerance_Parameter - tmp_pidx_s) *
                                      SMTCell::getMetalOneStep() >=
                              SMTCell::getRealNumTrackV() - 1
                          ? (SMTCell::getRealNumTrackV() - 1)
                          : (col + (tolerance_Parameter - tmp_pidx_s) *
                                             SMTCell::getMetalOneStep() >=
                                     0
                                 ? (col + (tolerance_Parameter - tmp_pidx_s) *
                                              SMTCell::getMetalOneStep())
                                 : (0)));

            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 8
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";8\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))))\n");
            SMTCell::writeConstraint(fmt::format(
                "	(ite (and (= ff{} true) (= ff{} false)) (ite (bvsge "
                "(bvadd x{} (_ bv{} {})) (bvadd x{} (_ bv{} {})))\n",
                inst_pin_s, inst_pin_t, inst_pin_s,
                (w_s - tmp_pidx_s) * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV(), inst_pin_t,
                tmp_pidx_t * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            tmp_bv = (col - (tolerance_Parameter + w_s - tmp_pidx_s) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + w_s - tmp_pidx_s) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 9
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";9\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");

            tmp_bv = (col + (tolerance_Parameter - tmp_pidx_t) *
                                      SMTCell::getMetalOneStep() >=
                              (SMTCell::getRealNumTrackV() - 1)
                          ? (SMTCell::getRealNumTrackV() - 1)
                          : (col + (tolerance_Parameter - tmp_pidx_t) *
                                             SMTCell::getMetalOneStep() >=
                                     0
                                 ? (col + (tolerance_Parameter - tmp_pidx_t) *
                                              SMTCell::getMetalOneStep())
                                 : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 10
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";10\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true)))\n");
            tmp_bv = (col - (tolerance_Parameter + tmp_pidx_t) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + tmp_pidx_t) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 11
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";11\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv =
                (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                 SMTCell::getMetalOneStep() >=
                         SMTCell::getRealNumTrackV() - 1
                     ? (SMTCell::getRealNumTrackV() - 1)
                     : (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                        SMTCell::getMetalOneStep() >=
                                0
                            ? (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                         SMTCell::getMetalOneStep())
                            : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt "
                "x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 12
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";12\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))))\n");
            SMTCell::writeConstraint(fmt::format(
                "	(ite (bvsge (bvadd x{} (_ bv{} {})) (bvadd x{} (_ bv{} "
                "{})))\n",
                inst_pin_s, (w_s - tmp_pidx_s) * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV(), inst_pin_t,
                (w_t - tmp_pidx_t) * SMTCell::getMetalOneStep(),
                SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            tmp_bv = (col - (tolerance_Parameter + w_s - tmp_pidx_s) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + w_s - tmp_pidx_s) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 13
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";13\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv =
                ((col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                            SMTCell::getMetalOneStep()) >=
                         (SMTCell::getRealNumTrackV() - 1)
                     ? (SMTCell::getRealNumTrackV() - 1)
                     : ((col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                                   SMTCell::getMetalOneStep()) >= 0
                            ? (col + (tolerance_Parameter - w_t + tmp_pidx_t) *
                                         SMTCell::getMetalOneStep())
                            : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);
            // fmt::print("13. bv:{}, w_t:{}\n", tmp_bv, w_t);
            // 14
            if (SMTCell::DEBUG)
              // SMTCell::writeConstraint(";14\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true)))\n");
            tmp_bv = (col - (tolerance_Parameter + w_t - tmp_pidx_t) *
                                      SMTCell::getMetalOneStep() >=
                              0
                          ? (col - (tolerance_Parameter + w_t - tmp_pidx_t) *
                                       SMTCell::getMetalOneStep())
                          : (0));
            SMTCell::writeConstraint(fmt::format(
                "             (and (ite (bvslt x{} (_ bv{} {})) (and",
                inst_pin_t, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 15
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";15\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))\n");
            tmp_bv =
                (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                 SMTCell::getMetalOneStep() >=
                         SMTCell::getRealNumTrackV() - 1
                     ? (SMTCell::getRealNumTrackV() - 1)
                     : (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                        SMTCell::getMetalOneStep() >=
                                0
                            ? (col + (tolerance_Parameter - w_s + tmp_pidx_s) *
                                         SMTCell::getMetalOneStep())
                            : (0)));
            SMTCell::writeConstraint(fmt::format(
                "                  (ite (bvsgt "
                "x{} (_ bv{} {})) (and",
                inst_pin_s, tmp_bv, SMTCell::getBitLengthNumTrackV()));
            SMTCell::cnt("l", 0);

            // 16
            if (SMTCell::DEBUG)
              SMTCell::writeConstraint(";16\n");
            FlowWriter::localize_commodity_helper(col, commodityIndex, netIndex,
                                                  false);

            SMTCell::writeConstraint(") (= true true))))))))\n");
            SMTCell::cnt("c", 1);
          }
        }
      }
    }
  }

  SMTCell::writeConstraint(";End of Localization\n\n");
}

void FlowWriter::localize_commodity_helper(int col, int commodityIndex,
                                           int netIndex, bool DEBUG) {
  std::string tmp_str = "";
  std::map<std::string, int> h_edge;
  int step = 0;
  for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
    for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
      // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
      //   continue;
      // }
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }

      Triplet vCoord = Triplet(metal, row, col);
      // incoming
      if (SMTCell::ifEdgeIn(vCoord.getVname())) {
        for (int i : SMTCell::getEdgeIn(vCoord.getVname())) {
          std::string metal_variable = fmt::format(
              "{}_{}", SMTCell::getUdEdge(i)->getUdFromEdge()->getVname(),
              vCoord.getVname());
          std::string variable_name =
              fmt::format("N{}_C{}_E_{}", SMTCell::getNet(netIndex)->getNetID(),
                          commodityIndex, metal_variable);
          if (h_edge.find(metal_variable) == h_edge.end()) {
            if (!SMTCell::ifAssigned(variable_name)) {
              SMTCell::setVar(variable_name, 2);
              SMTCell::writeConstraint(
                  fmt::format(" (= {} false)", variable_name));
              h_edge[metal_variable] = 1;
              SMTCell::cnt("l", 1);
            }
          }
        }
      }

      // outgoing
      if (SMTCell::ifEdgeOut(vCoord.getVname())) {
        for (int i : SMTCell::getEdgeOut(vCoord.getVname())) {
          std::string metal_variable =
              fmt::format("{}_{}", vCoord.getVname(),
                          SMTCell::getUdEdge(i)->getUdToEdge()->getVname());
          std::string variable_name =
              fmt::format("N{}_C{}_E_{}", SMTCell::getNet(netIndex)->getNetID(),
                          commodityIndex, metal_variable);
          if (h_edge.find(metal_variable) == h_edge.end()) {
            if (!SMTCell::ifAssigned(variable_name)) {
              SMTCell::setVar(variable_name, 2);
              SMTCell::writeConstraint(
                  fmt::format(" (= {} false)", variable_name));
              h_edge[metal_variable] = 1;
              SMTCell::cnt("l", 1);
            }
          }
        }
      }

      // sink
      if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
        for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
          std::string metal_variable =
              fmt::format("{}_{}", vCoord.getVname(),
                          SMTCell::getVirtualEdge(i)->getPinName());
          if (h_edge.find(metal_variable) == h_edge.end()) {
            if (SMTCell::getVirtualEdge(i)->getPinName() ==
                    SMTCell::getNet(netIndex)->getSource_ofNet() ||
                SMTCell::getVirtualEdge(i)->getPinName() ==
                    SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex)) {
              tmp_str = fmt::format("N{}_C{}_E_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex, metal_variable);
              if (!SMTCell::ifAssigned(tmp_str)) {
                SMTCell::setVar(tmp_str, 2);
                SMTCell::writeConstraint(fmt::format(" (= {} false)", tmp_str));
                h_edge[metal_variable] = 1;
                SMTCell::cnt("l", 1);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * initialize commodity flow variable:
 * Initialize Net/Commodity/Edge Variable
 * 
 * @param   void
 *
 * @return  void
 */
void FlowWriter::init_commodity_flow_var() {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
           vEdgeIndex++) {
        std::string tmp_vname = "";
        // ignoring $virtualEdges[$vEdgeIndex][2] =~ /^pin/ since this is always
        // a pin name
        if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
            SMTCell::getNet(netIndex)->getSource_ofNet()) {
          // ### GATE Pin
          if (SMTCell::getPin(SMTCell::getNet(netIndex)->getSource_ofNet())
                  ->getPinType() == "G") {
            int col = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
            // Gate on odd col
            if (SMTCell::ifSDCol(col)) {
              std::string variable_name = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex,
                  SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                  SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());

              SMTCell::assignFalseVar(variable_name);
            }
          } else {
            int col = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
            // Gate on even col
            if (SMTCell::ifGCol(col)) {
              std::string variable_name = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex,
                  SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                  SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());

              SMTCell::assignFalseVar(variable_name);
            }
          }
        } else if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
                   SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex)) {
          if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() !=
              Pin::keySON) {
            if (SMTCell ::getPin(
                    SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex))
                    ->getPinType() == "G") {
              int col = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
              if (SMTCell::ifSDCol(col)) {
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex,
                    SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                    SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());

                SMTCell::assignFalseVar(variable_name);
              }
            } else {
              int col = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
              if (SMTCell::ifGCol(col)) {
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex,
                    SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                    SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());

                SMTCell::assignFalseVar(variable_name);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * Flow capacity control:
 * Indicating Source/Sink Max flow
 * 
 * @param   void
 *
 * @return  void
 */
void FlowWriter::write_flow_capacity_control() {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      std::string tmp_vname = "";
      int startIdx = 0;
      int endIdx = 0;
      int instIdx = 0;

      int upRow = 0;
      int lowRow = 0;
      int beginRow = 0;
      int endRow = 0;
      int c_l = 0;
      int c_u = 0;

      // ## Source MaxFlow Indicator
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();

      // external net should NOT be considered
      // if (pidx_s == Pin::keySON) {
      //   continue;
      // }

      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
        upRow = SMTCell::getRoutingTrack(
            SMTCell::getNumPTrackH() - 1 -
            SMTCell::getConnection(
                SMTCell::getInst(source_inst_idx)->getInstWidth() /
                tmp_finger_source[0]));
        lowRow = SMTCell::getRoutingTrack(SMTCell::getNumPTrackH() - 1);
        beginRow = 0;
        endRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 2;
        c_l = 0;
        c_u = SMTCell::getRealNumTrackV() - 1;
      } else {
        upRow = SMTCell::getRoutingTrack(0);
        lowRow = SMTCell::getRoutingTrack(SMTCell::getConnection(
            SMTCell::getInst(source_inst_idx)->getInstWidth() /
            tmp_finger_source[0]));
        beginRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 1;
        endRow = SMTCell::getNumTrackH() - 3;
        c_l = 0;
        c_u = SMTCell::getRealNumTrackV() - 1;
      }

      for (int col = c_l; col <= c_u; col += SMTCell::getMetalOneStep()) {
        // ### GATE Pin
        if (source_pin->getPinType() == "G") {
          int tmp_pidx_s = std::stoi(
              std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          // SMTCell::writeConstraint(";Source Flow Indicator: GATE Pin\n");
          if (SMTCell::ifGCol(col)) {
            for (int j = 0; j < tmp_finger_source.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_source[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_source[j] * 2 + 1;
              if (tmp_pidx_s >= startIdx && tmp_pidx_s <= endIdx - 1) {
                if (tmp_pidx_s % 2 == 1) {
                  if (j == 0) {
                    if (tmp_pidx_s * SMTCell::getMetalOneStep() > col) {
                      for (int row = beginRow; row <= endRow; row++) {
                        if (SMTCell::findTrack(row) && lowRow <= row &&
                            upRow >= row) {
                          Triplet vCoord = Triplet(1, row, col);
                          tmp_vname = fmt::format(
                              "N{}_C{}_E_{}_{}",
                              SMTCell::getNet(netIndex)->getNetID(),
                              commodityIndex, vCoord.getVname(),
                              SMTCell::getNet(netIndex)->getSource_ofNet());
                          SMTCell::assignTrueVar(tmp_vname, 0, true);
                        }
                      }
                    } else {
                      int len = SMTCell::getBitLengthNumTrackV();
                      std::string tmp_str = "";
                      std::vector<std::string> tmp_var;
                      int cnt_var = 0;
                      int cnt_true = 0;

                      for (int row = beginRow; row <= endRow; row++) {
                        Triplet vCoord = Triplet(1, row, col);
                        std::string variable_name = fmt::format(
                            "N{}_C{}_E_{}_{}",
                            SMTCell::getNet(netIndex)->getNetID(),
                            commodityIndex, vCoord.getVname(),
                            SMTCell::getNet(netIndex)->getSource_ofNet());
                        if (SMTCell::findTrack(row) && lowRow <= row &&
                            upRow >= row) {
                          if (!SMTCell::ifAssigned(variable_name)) {
                            tmp_var.push_back(variable_name);
                            SMTCell::setVar(variable_name, 2);
                            cnt_var++;
                          } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                            SMTCell::setVar_wo_cnt(variable_name, 2);
                            cnt_true++;
                          }
                        }
                      }

                      if (cnt_true > 1) {
                        fmt::print("[ERROR] at-leat 2 variables are true in "
                                   "the exactly 1 clause!!\n");
                        exit(0);
                      } else if (cnt_var > 0) {
                        SMTCell::writeConstraint(fmt::format(
                            "(assert (ite (= x{} (_ bv{} {}))", source_inst_idx,
                            (col - tmp_pidx_s * SMTCell::getMetalOneStep()),
                            SMTCell::getBitLengthNumTrackV()));
                        SMTCell::cnt("l", 0);
                        if (cnt_true == 1) {
                          SMTCell::writeConstraint(" (and");
                          // assign false
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" (= {} false)", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(") (and");
                        } else {
                          SMTCell::writeConstraint(" (and ((_ at-least 1)");
                          // AL1 literal
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" {}", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(") ((_ at-most 1)");
                          // AM1 literal
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" {}", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(")) (and");
                        }
                        // assign false
                        for (int m = 0; m < tmp_var.size(); m++) {
                          SMTCell::writeConstraint(
                              fmt::format(" (= {} false)", tmp_var[m]));
                          SMTCell::cnt("l", 1);
                        }

                        SMTCell::writeConstraint(")))\n");
                        SMTCell::cnt("c", 1);
                      }
                    }
                  }
                  break;
                }
              }
            }
          }
        } else if (source_pin->getPinType() == "S") { // ### Source Pin
          int tmp_pidx_s = std::stoi(
              std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          int isValid = 0;
          std::string tmp_str_1;
          // std::string tmp_str_1 = ";Source Flow Indicator: Source Pin\n";

          if (SMTCell::ifSDCol(col)) {
            for (int j = 0; j < tmp_finger_source.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_source[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_source[j] * 2 + 1;
              if (tmp_pidx_s >= startIdx && tmp_pidx_s <= endIdx - 1) {
                if (tmp_pidx_s % 4 == 0) {
                  if (j == 0) {
                    if (tmp_pidx_s * SMTCell::getMetalOneStep() <= col) {
                      isValid = 1;
                      tmp_str_1 +=
                          fmt::format("(assert (ite (or (and (= ff{} false)",
                                      source_inst_idx);
                      SMTCell::cnt("l", 0);
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", source_inst_idx,
                          (col - tmp_pidx_s * SMTCell::getMetalOneStep()),
                          SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }
            startIdx = 0;
            endIdx = 0;

            for (int j = 0; j < tmp_finger_source.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_source[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_source[j] * 2 + 1;
              if (tmp_pidx_s >= startIdx && tmp_pidx_s <= endIdx - 1) {
                if (tmp_pidx_s % 4 == 0) {
                  if (j == 0) {
                    int tmp_col =
                        (((startIdx + endIdx - 1 - tmp_pidx_s) % 2 == 0
                              ? (startIdx + endIdx - 1 - tmp_pidx_s) *
                                    SMTCell::getMetalOneStep()
                              : (startIdx + endIdx - 1 - tmp_pidx_s + 1) *
                                    SMTCell::getMetalOneStep()));
                    if (tmp_col <= col) {
                      if (isValid == 0) {
                        tmp_str_1 +=
                            fmt::format("(assert (ite (or (and (= ff{} true)",
                                        source_inst_idx);
                        SMTCell::cnt("l", 0);
                        isValid = 1;
                      } else {
                        tmp_str_1 +=
                            fmt::format(" (and (= ff{} true)", source_inst_idx);
                        SMTCell::cnt("l", 0);
                      }
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", source_inst_idx,
                          (col - tmp_col), SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }

            if (isValid == 1) {
              std::string tmp_str = "";
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              for (int row = beginRow; row <= endRow; row++) {
                Triplet vCoord = Triplet(1, row, col);
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex, vCoord.getVname(),
                    SMTCell::getNet(netIndex)->getSource_ofNet());
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                    SMTCell::setVar_wo_cnt(variable_name, 2);
                    cnt_true++;
                  }
                }
              }

              if (cnt_true > 1) {
                fmt::print("[ERROR] at-leat 2 variables are true in "
                           "the exactly 1 clause!!\n");
                exit(0);
              } else if (cnt_var > 0) {
                SMTCell::writeConstraint(tmp_str_1);

                if (cnt_true == 1) {
                  SMTCell::writeConstraint(") (and");
                  // assign false
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(
                        fmt::format(" (= {} false)", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") (and");
                } else {
                  SMTCell::writeConstraint(") (and ((_ at-least 1)");
                  // AL1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") ((_ at-most 1)");
                  // AM1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(")) (and");
                }
                // assign false
                for (int m = 0; m < tmp_var.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(")))\n");
                SMTCell::cnt("c", 1);
              }
            } else {
              for (int row = beginRow; row <= endRow; row++) {
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  Triplet vCoord = Triplet(1, row, col);
                  std::string variable_name = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(),
                      SMTCell::getNet(netIndex)->getSource_ofNet());
                  SMTCell::assignTrueVar(variable_name, 0, true);
                }
              }
            }
          }
        } else if (source_pin->getPinType() == "D") { // ### Drain Pin
          // mergeable with source pin above
          int tmp_pidx_s = std::stoi(
              std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          int isValid = 0;
          std::string tmp_str_1;
          // std::string tmp_str_1 = ";Source Flow Indicator: Drain Pin\n";

          if (SMTCell::ifSDCol(col)) {
            for (int j = 0; j < tmp_finger_source.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_source[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_source[j] * 2 + 1;
              if (tmp_pidx_s >= startIdx && tmp_pidx_s <= endIdx - 1) {
                if (tmp_pidx_s % 4 == 2) {
                  if (j == 0) {
                    if (tmp_pidx_s * SMTCell::getMetalOneStep() <= col) {
                      isValid = 1;
                      tmp_str_1 +=
                          fmt::format("(assert (ite (or (and (= ff{} false)",
                                      source_inst_idx);
                      SMTCell::cnt("l", 0);
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", source_inst_idx,
                          (col - tmp_pidx_s * SMTCell::getMetalOneStep()),
                          SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }
            startIdx = 0;
            endIdx = 0;

            for (int j = 0; j < tmp_finger_source.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_source[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_source[j] * 2 + 1;
              if (tmp_pidx_s >= startIdx && tmp_pidx_s <= endIdx - 1) {
                if (tmp_pidx_s % 4 == 2) {
                  if (j == 0) {
                    int tmp_col =
                        (((startIdx + endIdx - 1 - tmp_pidx_s) % 2 == 0
                              ? (startIdx + endIdx - 1 - tmp_pidx_s) *
                                    SMTCell::getMetalOneStep()
                              : (startIdx + endIdx - 1 - tmp_pidx_s + 1) *
                                    SMTCell::getMetalOneStep()));
                    if (tmp_col <= col) {
                      if (isValid == 0) {
                        tmp_str_1 +=
                            fmt::format("(assert (ite (or (and (= ff{} true)",
                                        source_inst_idx);
                        SMTCell::cnt("l", 0);
                        isValid = 1;
                      } else {
                        tmp_str_1 +=
                            fmt::format(" (and (= ff{} true)", source_inst_idx);
                        SMTCell::cnt("l", 0);
                      }
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", source_inst_idx,
                          (col - tmp_col), SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }

            if (isValid == 1) {
              std::string tmp_str = "";
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              for (int row = beginRow; row <= endRow; row++) {
                Triplet vCoord = Triplet(1, row, col);
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex, vCoord.getVname(),
                    SMTCell::getNet(netIndex)->getSource_ofNet());
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                    SMTCell::setVar_wo_cnt(variable_name, 2);
                    cnt_true++;
                  }
                }
              }

              if (cnt_true > 1) {
                fmt::print("[ERROR] at-leat 2 variables are true in "
                           "the exactly 1 clause!!\n");
                exit(0);
              } else if (cnt_var > 0) {
                SMTCell::writeConstraint(tmp_str_1);

                if (cnt_true == 1) {
                  SMTCell::writeConstraint(") (and");
                  // assign false
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(
                        fmt::format(" (= {} false)", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") (and");
                } else {
                  SMTCell::writeConstraint(") (and ((_ at-least 1)");
                  // AL1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") ((_ at-most 1)");
                  // AM1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(")) (and");
                }
                // assign false
                for (int m = 0; m < tmp_var.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(")))\n");
                SMTCell::cnt("c", 1);
              }
            } else {
              for (int row = beginRow; row <= endRow; row++) {
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  Triplet vCoord = Triplet(1, row, col);
                  std::string variable_name = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(),
                      SMTCell::getNet(netIndex)->getSource_ofNet());
                  SMTCell::assignTrueVar(variable_name, 0, true);
                }
              }
            }
          }
        }
      }

      // ## Sink MaxFlow Indicator
      // mergeable with Source MaxFlow Indicator above
      std::string pidx_t =
          SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
      // external net should NOT be considered
      if (pidx_t == Pin::keySON) {
        continue;
      }

      Pin *sink_pin = SMTCell::getPin(pidx_t);
      int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

      std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(sink_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
        upRow = SMTCell::getRoutingTrack(
            SMTCell::getNumPTrackH() - 1 -
            SMTCell::getConnection(
                SMTCell::getInst(sink_inst_idx)->getInstWidth() /
                tmp_finger_sink[0]));
        lowRow = SMTCell::getRoutingTrack(SMTCell::getNumPTrackH() - 1);
        beginRow = 0;
        endRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 2;
        c_l = 0;
        c_u = SMTCell::getRealNumTrackV() - 1;
      } else {
        upRow = SMTCell::getRoutingTrack(0);
        lowRow = SMTCell::getRoutingTrack(SMTCell::getConnection(
            SMTCell::getInst(sink_inst_idx)->getInstWidth() /
            tmp_finger_sink[0]));
        beginRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 1;
        endRow = SMTCell::getNumTrackH() - 3;
        c_l = 0;
        c_u = SMTCell::getRealNumTrackV() - 1;
      }

      for (int col = c_l; col <= c_u; col += SMTCell::getMetalOneStep()) {
        // ### GATE Pin
        if (sink_pin->getPinType() == "G") {
          int tmp_pidx_t = std::stoi(
              std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          // SMTCell::writeConstraint(";Sink Flow Indicator: GATE Pin\n");

          if (SMTCell::ifGCol(col)) {
            for (int j = 0; j < tmp_finger_sink.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_sink[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_sink[j] * 2 + 1;
              if (tmp_pidx_t >= startIdx && tmp_pidx_t <= endIdx - 1) {
                if (tmp_pidx_t % 2 == 1) {
                  if (j == 0) {
                    if (tmp_pidx_t * SMTCell::getMetalOneStep() > col) {
                      for (int row = beginRow; row <= endRow; row++) {
                        if (SMTCell::findTrack(row) && lowRow <= row &&
                            upRow >= row) {
                          Triplet vCoord = Triplet(1, row, col);
                          tmp_vname = fmt::format(
                              "N{}_C{}_E_{}_{}",
                              SMTCell::getNet(netIndex)->getNetID(),
                              commodityIndex, vCoord.getVname(), pidx_t);
                          SMTCell::assignTrueVar(tmp_vname, 0, true);
                        }
                      }
                    } else {
                      int len = SMTCell::getBitLengthNumTrackV();
                      std::string tmp_str = "";
                      std::vector<std::string> tmp_var;
                      int cnt_var = 0;
                      int cnt_true = 0;

                      for (int row = beginRow; row <= endRow; row++) {
                        Triplet vCoord = Triplet(1, row, col);
                        std::string variable_name = fmt::format(
                            "N{}_C{}_E_{}_{}",
                            SMTCell::getNet(netIndex)->getNetID(),
                            commodityIndex, vCoord.getVname(), pidx_t);
                        if (SMTCell::findTrack(row) && lowRow <= row &&
                            upRow >= row) {
                          if (!SMTCell::ifAssigned(variable_name)) {
                            tmp_var.push_back(variable_name);
                            SMTCell::setVar(variable_name, 2);
                            cnt_var++;
                          } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                            SMTCell::setVar_wo_cnt(variable_name, 2);
                            cnt_true++;
                          }
                        }
                      }

                      if (cnt_true > 1) {
                        fmt::print("[ERROR] at-leat 2 variables are true in "
                                   "the exactly 1 clause!!\n");
                        exit(0);
                      } else if (cnt_var > 0) {
                        SMTCell::writeConstraint(fmt::format(
                            "(assert (ite (= x{} (_ bv{} {}))", sink_inst_idx,
                            (col - tmp_pidx_t * SMTCell::getMetalOneStep()),
                            SMTCell::getBitLengthNumTrackV()));
                        SMTCell::cnt("l", 0);
                        if (cnt_true == 1) {
                          SMTCell::writeConstraint(" (and");
                          // assign false
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" (= {} false)", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(") (and");
                        } else {
                          SMTCell::writeConstraint(" (and ((_ at-least 1)");
                          // AL1 literal
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" {}", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(") ((_ at-most 1)");
                          // AM1 literal
                          for (int m = 0; m < tmp_var.size(); m++) {
                            SMTCell::writeConstraint(
                                fmt::format(" {}", tmp_var[m]));
                            SMTCell::cnt("l", 1);
                          }
                          SMTCell::writeConstraint(")) (and");
                        }
                        // assign false
                        for (int m = 0; m < tmp_var.size(); m++) {
                          SMTCell::writeConstraint(
                              fmt::format(" (= {} false)", tmp_var[m]));
                          SMTCell::cnt("l", 1);
                        }

                        SMTCell::writeConstraint(")))\n");
                        SMTCell::cnt("c", 1);
                      }
                    }
                  }
                  break;
                }
              }
            }
          }
        } else if (sink_pin->getPinType() == "S") { // ### Source Pin
          int tmp_pidx_t = std::stoi(
              std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          int isValid = 0;
          std::string tmp_str_1;
          // std::string tmp_str_1 = ";Sink Flow Indicator: Source Pin\n";

          if (SMTCell::ifSDCol(col)) {
            for (int j = 0; j < tmp_finger_sink.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_sink[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_sink[j] * 2 + 1;
              if (tmp_pidx_t >= startIdx && tmp_pidx_t <= endIdx - 1) {
                if (tmp_pidx_t % 4 == 0) {
                  if (j == 0) {
                    if (tmp_pidx_t * SMTCell::getMetalOneStep() <= col) {
                      isValid = 1;
                      tmp_str_1 +=
                          fmt::format("(assert (ite (or (and (= ff{} false)",
                                      sink_inst_idx);
                      SMTCell::cnt("l", 0);
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", sink_inst_idx,
                          (col - tmp_pidx_t * SMTCell::getMetalOneStep()),
                          SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }
            startIdx = 0;
            endIdx = 0;

            for (int j = 0; j < tmp_finger_sink.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_sink[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_sink[j] * 2 + 1;
              if (tmp_pidx_t >= startIdx && tmp_pidx_t <= endIdx - 1) {
                if (tmp_pidx_t % 4 == 0) {
                  if (j == 0) {
                    int tmp_col =
                        (((startIdx + endIdx - 1 - tmp_pidx_t) % 2 == 0
                              ? (startIdx + endIdx - 1 - tmp_pidx_t) *
                                    SMTCell::getMetalOneStep()
                              : (startIdx + endIdx - 1 - tmp_pidx_t + 1) *
                                    SMTCell::getMetalOneStep()));
                    if (tmp_col <= col) {
                      if (isValid == 0) {
                        tmp_str_1 +=
                            fmt::format("(assert (ite (or (and (= ff{} true)",
                                        sink_inst_idx);
                        SMTCell::cnt("l", 0);
                        isValid = 1;
                      } else {
                        tmp_str_1 +=
                            fmt::format(" (and (= ff{} true)", sink_inst_idx);
                        SMTCell::cnt("l", 0);
                      }
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", sink_inst_idx,
                          (col - tmp_col), SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }

            if (isValid == 1) {
              std::string tmp_str = "";
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              for (int row = beginRow; row <= endRow; row++) {
                Triplet vCoord = Triplet(1, row, col);
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex, vCoord.getVname(), pidx_t);
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                    SMTCell::setVar_wo_cnt(variable_name, 2);
                    cnt_true++;
                  }
                }
              }

              if (cnt_true > 1) {
                fmt::print("[ERROR] at-leat 2 variables are true in "
                           "the exactly 1 clause!!\n");
                exit(0);
              } else if (cnt_var > 0) {
                SMTCell::writeConstraint(tmp_str_1);

                if (cnt_true == 1) {
                  SMTCell::writeConstraint(") (and");
                  // assign false
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(
                        fmt::format(" (= {} false)", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") (and");
                } else {
                  SMTCell::writeConstraint(") (and ((_ at-least 1)");
                  // AL1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") ((_ at-most 1)");
                  // AM1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(")) (and");
                }
                // assign false
                for (int m = 0; m < tmp_var.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(")))\n");
                SMTCell::cnt("c", 1);
              }
            } else {
              for (int row = beginRow; row <= endRow; row++) {
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  Triplet vCoord = Triplet(1, row, col);
                  std::string variable_name = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(), pidx_t);
                  SMTCell::assignTrueVar(variable_name, 0, true);
                }
              }
            }
          }
        } else if (sink_pin->getPinType() == "D") { // ### Drain Pin
          // mergeable with source pin above
          int tmp_pidx_t = std::stoi(
              std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));
          startIdx = 0;
          endIdx = 0;
          int isValid = 0;
          std::string tmp_str_1;
          // std::string tmp_str_1 = ";Sink Flow Indicator: Drain Pin\n";

          if (SMTCell::ifSDCol(col)) {
            for (int j = 0; j < tmp_finger_sink.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_sink[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_sink[j] * 2 + 1;
              if (tmp_pidx_t >= startIdx && tmp_pidx_t <= endIdx - 1) {
                if (tmp_pidx_t % 4 == 2) {
                  if (j == 0) {
                    if (tmp_pidx_t * SMTCell::getMetalOneStep() <= col) {
                      isValid = 1;
                      tmp_str_1 +=
                          fmt::format("(assert (ite (or (and (= ff{} false)",
                                      sink_inst_idx);
                      SMTCell::cnt("l", 0);
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", sink_inst_idx,
                          (col - tmp_pidx_t * SMTCell::getMetalOneStep()),
                          SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }
            startIdx = 0;
            endIdx = 0;

            for (int j = 0; j < tmp_finger_sink.size(); j++) {
              if (j > 0) {
                startIdx = tmp_finger_sink[j - 1] * 2 + 1;
              }

              endIdx = tmp_finger_sink[j] * 2 + 1;
              if (tmp_pidx_t >= startIdx && tmp_pidx_t <= endIdx - 1) {
                if (tmp_pidx_t % 4 == 2) {
                  if (j == 0) {
                    int tmp_col =
                        (((startIdx + endIdx - 1 - tmp_pidx_t) % 2 == 0
                              ? (startIdx + endIdx - 1 - tmp_pidx_t) *
                                    SMTCell::getMetalOneStep()
                              : (startIdx + endIdx - 1 - tmp_pidx_t + 1) *
                                    SMTCell::getMetalOneStep()));
                    if (tmp_col <= col) {
                      if (isValid == 0) {
                        tmp_str_1 +=
                            fmt::format("(assert (ite (or (and (= ff{} true)",
                                        sink_inst_idx);
                        SMTCell::cnt("l", 0);
                        isValid = 1;
                      } else {
                        tmp_str_1 +=
                            fmt::format(" (and (= ff{} true)", sink_inst_idx);
                        SMTCell::cnt("l", 0);
                      }
                      tmp_str_1 += fmt::format(
                          " (= x{} (_ bv{} {})))", sink_inst_idx,
                          (col - tmp_col), SMTCell::getBitLengthNumTrackV());
                      SMTCell::cnt("l", 0);
                    }
                  }
                  break;
                }
              }
            }

            if (isValid == 1) {
              std::string tmp_str = "";
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              for (int row = beginRow; row <= endRow; row++) {
                Triplet vCoord = Triplet(1, row, col);
                std::string variable_name = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex, vCoord.getVname(), pidx_t);
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  if (!SMTCell::ifAssigned(variable_name)) {
                    tmp_var.push_back(variable_name);
                    SMTCell::setVar(variable_name, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssignedTrue(tmp_vname)) {
                    SMTCell::setVar_wo_cnt(variable_name, 2);
                    cnt_true++;
                  }
                }
              }

              if (cnt_true > 1) {
                fmt::print("[ERROR] at-leat 2 variables are true in "
                           "the exactly 1 clause!!\n");
                exit(0);
              } else if (cnt_var > 0) {
                SMTCell::writeConstraint(tmp_str_1);

                if (cnt_true == 1) {
                  SMTCell::writeConstraint(") (and");
                  // assign false
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(
                        fmt::format(" (= {} false)", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") (and");
                } else {
                  SMTCell::writeConstraint(") (and ((_ at-least 1)");
                  // AL1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") ((_ at-most 1)");
                  // AM1 literal
                  for (int m = 0; m < tmp_var.size(); m++) {
                    SMTCell::writeConstraint(fmt::format(" {}", tmp_var[m]));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(")) (and");
                }
                // assign false
                for (int m = 0; m < tmp_var.size(); m++) {
                  SMTCell::writeConstraint(
                      fmt::format(" (= {} false)", tmp_var[m]));
                  SMTCell::cnt("l", 1);
                }

                SMTCell::writeConstraint(")))\n");
                SMTCell::cnt("c", 1);
              }
            } else {
              for (int row = beginRow; row <= endRow; row++) {
                if (SMTCell::findTrack(row) && lowRow <= row && upRow >= row) {
                  Triplet vCoord = Triplet(1, row, col);
                  std::string variable_name = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(), pidx_t);
                  SMTCell::assignTrueVar(variable_name, 0, true);
                }
              }
            }
          }
        }
      }
    }
  }
}

/**
 * Flow capacity control:
 * Indicating Source/Sink Max flow
 * 
 * @param   *fp             output file pointer
 * @param   EXT_Parameter   external parameter
 *
 * @return  void
 */
void FlowWriter::write_flow_conservation(FILE *fp, int EXT_Parameter) {
  SMTCell::writeConstraint(";1. Commodity flow conservation for each vertex "
                           "and every connected edge to the vertex\n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      int step = 0;
      for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
        if (metal == 1) {
          step = SMTCell::getMetalOneStep();
        } else if (metal >= 3) {
          step = SMTCell::getMetalThreeStep();
        } else {
          // # Metal 2 (M0)
          step = SMTCell::getGCDStep();
        }
        for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
          for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
               col += step) {
            if (col % SMTCell::getMetalOneStep() != 0 &&
                col % SMTCell::getMetalThreeStep() != 0) {
              continue;
            }
            // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
            //   continue;
            // }
            Triplet vCoord = Triplet(metal, row, col);
            std::string tmp_str = "";         // building literal
            std::vector<std::string> tmp_var; // store all clauses
            int cnt_var = 0;
            int cnt_true = 0;

            if (SMTCell::ifEdgeIn(vCoord.getVname())) {
              // incoming
              for (int i : SMTCell::getEdgeIn(vCoord.getVname())) {
                tmp_str = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex,
                    SMTCell::getUdEdge(i)->getUdFromEdge()->getVname(),
                    vCoord.getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
              }
            }

            if (SMTCell::ifEdgeOut(vCoord.getVname())) {
              // outcoming
              for (int i : SMTCell::getEdgeOut(vCoord.getVname())) {
                tmp_str = fmt::format(
                    "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                    commodityIndex, vCoord.getVname(),
                    SMTCell::getUdEdge(i)->getUdToEdge()->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
              }
            }

            if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
              // sink
              for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
                if (SMTCell::getVirtualEdge(i)->getPinName() ==
                        SMTCell::getNet(netIndex)->getSource_ofNet() ||
                    SMTCell::getVirtualEdge(i)->getPinName() ==
                        SMTCell::getNet(netIndex)->getSinks_inNet(
                            commodityIndex)) {
                  tmp_str = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(),
                      SMTCell::getVirtualEdge(i)->getPinName());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 2) {
                fmt::print("[ERROR] number of true commodity variable exceed "
                           "2!! in Vertex[$vName]\n");
                exit(-1);
              } else if (cnt_true > 1) {
                // # if # of true variables is two, then remained variables
                // should be false
                SMTCell::assignTrueVar(tmp_var[0], 0, true);
              } else {
                // # if # of true variables is one, then remained variable
                // should be exactly one
                if (cnt_var > 1) {
                  SMTCell::assignTrueVar(tmp_var[0], 1, true);
                  SMTCell::setVar_wo_cnt(tmp_var[0], 0);
                } else if (cnt_var > 1) {
                  // # at-most 1
                  SMTCell::writeConstraint("(assert ((_ at-most 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    ;
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                  // # at-least 1
                  SMTCell::writeConstraint("(assert ((_ at-least 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    ;
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                }
              }
            } else {
              // # true-assigned variable is not included in terms
              // # if # of rest variables is one, then that variable should be
              // false
              if (cnt_var == 1) {
                SMTCell::assignTrueVar(tmp_var[0], 0, true);
              } else if (cnt_var == 2) {
                SMTCell::writeConstraint(
                    fmt::format("(assert (= (or (not {}) {}) true))\n",
                                tmp_var[0], tmp_var[1]));
                SMTCell::cnt("l", 1);
                SMTCell::cnt("l", 1);
                SMTCell::cnt("c", 1);
                SMTCell::writeConstraint(
                    fmt::format("(assert (= (or {} (not {})) true))\n",
                                tmp_var[0], tmp_var[1]));
                SMTCell::cnt("l", 1);
                SMTCell::cnt("l", 1);
                SMTCell::cnt("c", 1);
              } else if (cnt_var > 2) {
                // #at-most 2
                SMTCell::writeConstraint("(assert ((_ at-most 2)");
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  ;
                  SMTCell::cnt("l", 1);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 1);
                // # not exactly-1
                for (auto s_i : tmp_var) {
                  SMTCell::writeConstraint("(assert (= (or");
                  for (auto s_j : tmp_var) {
                    if (s_i == s_j) {
                      SMTCell::writeConstraint(fmt::format(" (not {})", s_j));
                    } else {
                      SMTCell::writeConstraint(fmt::format(" {}", s_j));
                    }
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint(") true))\n");
                  SMTCell::cnt("c", 1);
                }
              }
            }
          }
        }
      }
    }
  }
  // ### Net Variables for CFC
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      // ########### It might be redundancy, some net don't need some pins
      // ..... ###########
      for (int pinIndex = 0; pinIndex < SMTCell::getPinCnt(); pinIndex++) {
        std::string pName = SMTCell::getPin(pinIndex)->getPinName();
        if (pName ==
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex)) {
          if (pName == Pin::keySON) {
            // Super Outer Node
            if (EXT_Parameter == 0) {
              std::string tmp_str = "";         // building literal
              std::vector<std::string> tmp_var; // store all clauses
              int cnt_var = 0;
              int cnt_true = 0;
              // sink
              if (SMTCell::ifVEdgeIn(pName)) {
                for (int i : SMTCell::getVEdgeIn(pName)) {
                  int metal = SMTCell::getVirtualEdge(i)->getVCoord()->metal_;
                  int row = SMTCell::getVirtualEdge(i)->getVCoord()->row_;
                  if (metal % 2 == 1 &&
                      (row == 0 || row == SMTCell::getNumTrackH() - 3)) {
                    tmp_str = fmt::format(
                        "N{}_C{}_E_{}_{}",
                        SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                        SMTCell::getVirtualEdge(i)->getVName(), pName);
                    if (!SMTCell::ifAssigned(tmp_str)) {
                      tmp_var.push_back(tmp_str);
                      SMTCell::setVar(tmp_str, 2);
                      cnt_var++;
                    } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                      SMTCell::setVar_wo_cnt(tmp_str, 0);
                      cnt_true++;
                    }
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  fmt::print(
                      "[ERROR] # of true pinSON in Net[$nets[$netIndex][1]] "
                      "Commodity[$commodityIndex] exceeds one!!\n");
                  exit(-1);
                } else {
                  // # if # of true variables is one, then remained variables
                  // should be false
                  for (auto s : tmp_var) {
                    SMTCell::assignTrueVar(s, 0, true);
                  }
                }
              } else {
                // # true-assigned variable is not included in terms
                if (cnt_var == 1) {
                  SMTCell::assignTrueVar(tmp_var[0], 1, true);
                  SMTCell::setVar_wo_cnt(tmp_var[0], 0);
                } else if (cnt_var > 0) {
                  // #at-most 1
                  SMTCell::writeConstraint("(assert ((_ at-most 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                  // #at-least 1
                  SMTCell::writeConstraint("(assert ((_ at-least 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                }
              }
            } else {
              std::string tmp_str = "";         // building literal
              std::vector<std::string> tmp_var; // store all clauses
              int cnt_var = 0;
              int cnt_true = 0;
              // sink
              if (SMTCell::ifVEdgeIn(pName)) {
                for (int i : SMTCell::getVEdgeIn(pName)) {
                  int metal = SMTCell::getVirtualEdge(i)->getVCoord()->metal_;
                  int row = SMTCell::getVirtualEdge(i)->getVCoord()->row_;
                  if (metal % 2 == 1) {
                    tmp_str = fmt::format(
                        "N{}_C{}_E_{}_{}",
                        SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                        SMTCell::getVirtualEdge(i)->getVName(), pName);
                    switch (SMTCell::assignVar(tmp_str)) {
                    case 1:
                      tmp_var.push_back(tmp_str);
                      cnt_var++;
                      break;
                    case 0:
                      cnt_true++;
                      break;
                    }
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  fmt::print(
                      "[ERROR] # of true pinSON in Net[$nets[$netIndex][1]] "
                      "Commodity[$commodityIndex] exceeds one!!\n");
                  exit(-1);
                } else {
                  // # if # of true variables is one, then remained variables
                  // should be false
                  for (auto s : tmp_var) {
                    SMTCell::assignTrueVar(s, 0, true);
                  }
                }
              } else {
                // # true-assigned variable is not included in terms
                if (cnt_var == 1) {
                  SMTCell::assignTrueVar(tmp_var[0], 1, true);
                  SMTCell::setVar_wo_cnt(tmp_var[0], 0);
                } else if (cnt_var > 0) {
                  // #at-most 1
                  SMTCell::writeConstraint("(assert ((_ at-most 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    ;
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                  // #at-least 1
                  SMTCell::writeConstraint("(assert ((_ at-least 1)");
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    ;
                    SMTCell::cnt("l", 1);
                  }
                  SMTCell::writeConstraint("))\n");
                  SMTCell::cnt("c", 1);
                }
              }
            }
          } else {
            int lowRow = 0;
            int upRow = 0;
            int instIdx = 0;
            // ## Sink MaxFlow Indicator
            if (instIdx <= SMTCell::getLastIdxPMOS()) {
              lowRow = 0;
              upRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 2;
            } else {
              lowRow = int(SMTCell::getNumTrackH() / 2 + 0.5) / 2 - 1;
              upRow = SMTCell::getNumTrackH() - 3;
            }

            for (int row = lowRow; row <= upRow; row++) {
              if (SMTCell::findTrack(row)) {
                std::string tmp_str = "";         // building literal
                std::vector<std::string> tmp_var; // store all clauses
                int cnt_var = 0;
                int cnt_true = 0;
                // sink
                if (SMTCell::ifVEdgeIn(pName)) {
                  for (int i : SMTCell::getVEdgeIn(pName)) {
                    tmp_str = fmt::format(
                        "N{}_C{}_E_{}_{}",
                        SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                        SMTCell::getVirtualEdge(i)->getVName(), pName);
                    switch (SMTCell::assignVar(tmp_str)) {
                    case 1:
                      tmp_var.push_back(tmp_str);
                      cnt_var++;
                      break;
                    case 0:
                      cnt_true++;
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    fmt::print("[ERROR] # of true pinSON in "
                               "Net[$nets[$netIndex][1]] "
                               "Commodity[$commodityIndex] exceeds one!!\n");
                    exit(-1);
                  } else {
                    // # if # of true variables is one, then remained
                    // variables should be false
                    for (auto s : tmp_var) {
                      SMTCell::assignTrueVar(s, 0, true);
                    }
                  }
                } else {
                  // # true-assigned variable is not included in terms
                  if (cnt_var == 1) {
                    SMTCell::assignTrueVar(tmp_var[0], 1, true);
                    SMTCell::setVar_wo_cnt(tmp_var[0], 0);
                  } else if (cnt_var > 0) {
                    // #at-most 1
                    SMTCell::writeConstraint("(assert ((_ at-most 1)");
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      ;
                      SMTCell::cnt("l", 1);
                    }
                    SMTCell::writeConstraint("))\n");
                    SMTCell::cnt("c", 1);
                    // #at-least 1
                    SMTCell::writeConstraint("(assert ((_ at-least 1)");
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      ;
                      SMTCell::cnt("l", 1);
                    }
                    SMTCell::writeConstraint("))\n");
                    SMTCell::cnt("c", 1);
                  }
                }
              }
            }
          }
        }

        if (pName == SMTCell::getNet(netIndex)->getSource_ofNet()) {
          int beginRow = 0;
          int endRow = 0;
          int instIdx = 0;
          // ## Source MaxFlow Indicator
          if (instIdx <= SMTCell::getLastIdxPMOS()) {
            beginRow = 0;
            endRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 2;
          } else {
            beginRow = int(SMTCell::getNumTrackH() / 2 + 0.5) - 1;
            endRow = SMTCell::getNumTrackH() - 3;
          }
          std::string tmp_str = "";         // building literal
          std::vector<std::string> tmp_var; // store all clauses
          int cnt_var = 0;
          int cnt_true = 0;
          // sink
          if (SMTCell::ifVEdgeIn(pName)) {
            for (int i : SMTCell::getVEdgeIn(pName)) {
              tmp_str = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex, SMTCell::getVirtualEdge(i)->getVName(),
                  pName);
              switch (SMTCell::assignVar(tmp_str)) {
              case 1:
                tmp_var.push_back(tmp_str);
                cnt_var++;
                break;
              case 0:
                cnt_true++;
                break;
              }
            }
          }
          if (cnt_true > 0) {
            if (cnt_true > 1) {
              fmt::print("[ERROR] # of true pinSON in Net[$nets[$netIndex][1]] "
                         "Commodity[$commodityIndex] exceeds one!!\n");
              exit(-1);
            } else {
              // # if # of true variables is one, then remained variables
              // should be false
              for (auto s : tmp_var) {
                SMTCell::assignTrueVar(s, 0, true);
              }
            }
          } else {
            // # true-assigned variable is not included in terms
            if (cnt_var == 1) {
              SMTCell::assignTrueVar(tmp_var[0], 1, true);
              SMTCell::setVar_wo_cnt(tmp_var[0], 0);
            } else if (cnt_var > 0) {
              // #at-most 1
              SMTCell::writeConstraint("(assert ((_ at-most 1)");
              for (auto s : tmp_var) {
                SMTCell::writeConstraint(fmt::format(" {}", s));
                ;
                SMTCell::cnt("l", 1);
              }
              SMTCell::writeConstraint("))\n");
              SMTCell::cnt("c", 1);
              // #at-least 1
              SMTCell::writeConstraint("(assert ((_ at-least 1)");
              for (auto s : tmp_var) {
                SMTCell::writeConstraint(fmt::format(" {}", s));
                ;
                SMTCell::cnt("l", 1);
              }
              SMTCell::writeConstraint("))\n");
              SMTCell::cnt("c", 1);
            }
          }
        }
      }
    }
  }

  std::string tmp_str = "";
  std::vector<std::string> tmp_var;
  int cnt_var = 0;
  int cnt_true = 0;

  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      int step = 0;
      for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
        if (metal == 1) {
          step = SMTCell::getMetalOneStep();
        } else if (metal >= 3) {
          step = SMTCell::getMetalThreeStep();
        } else {
          // # Metal 2 (M0)
          step = SMTCell::getGCDStep();
        }
        for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
          for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
               col += step) {
            if (col % SMTCell::getMetalOneStep() != 0 &&
                col % SMTCell::getMetalThreeStep() != 0) {
              continue;
            }
            // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
            //   continue;
            // }
            Triplet vCoord = Triplet(metal, row, col);
            // sink
            if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
              for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
                if (SMTCell::getVirtualEdge(i)->getPinName() ==
                        SMTCell::getNet(netIndex)->getSinks_inNet(
                            commodityIndex) &&
                    SMTCell::getVirtualEdge(i)->getPinName() == Pin::keySON) {
                  tmp_str = fmt::format(
                      "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      commodityIndex, vCoord.getVname(),
                      SMTCell::getVirtualEdge(i)->getPinName());
                  switch (SMTCell::assignVar(tmp_str)) {
                  case 1:
                    tmp_var.push_back(tmp_str);
                    cnt_var++;
                    break;
                  case 0:
                    cnt_true++;
                    break;
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  if (cnt_true > 0) {
    if (cnt_true > SMTCell::getOuterPinCnt()) {
      fmt::print("[ERROR] # of true pinSON exceeds $numOuterPins!!\n");
      exit(-1);
    } else if (cnt_true == SMTCell::getOuterPinCnt()) {
      // # if # of true variables is the same as # of outerpins, then remained
      // variables should be false
      for (auto s : tmp_var) {
        SMTCell::assignTrueVar(s, 0, true);
      }
    } else {
      // # at-most $numOuterPins-$cnt_true
      SMTCell::writeConstraint(fmt::format(
          "(assert ((_ at-most {})", (SMTCell::getOuterPinCnt() - cnt_true)));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
      // # at-least $numOuterPins-$cnt_true
      SMTCell::writeConstraint(fmt::format(
          "(assert ((_ at-least {})", (SMTCell::getOuterPinCnt() - cnt_true)));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
    }
  } else {
    if (cnt_var > 0) {
      // #at-most numOuterPins
      SMTCell::writeConstraint(
          fmt::format("(assert ((_ at-most {})", SMTCell::getOuterPinCnt()));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
      // #at-least numOuterPins
      SMTCell::writeConstraint(
          fmt::format("(assert ((_ at-least {})", SMTCell::getOuterPinCnt()));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
    }
  }

  std::cout << "has been written.\n";
}

/**
 * Vertex Exclusiveness:
 * No duplication in usage of vertex
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void FlowWriter::write_vertex_exclusive(FILE *fp) {
  SMTCell::writeConstraint(";2. Exclusiveness use of vertex for each vertex "
                           "and every connected edge to the vertex\n");
  int step = 0;
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
        //   continue;
        // }
        Triplet vCoord = {metal, row, col};
        int cnt_true_net = 0;
        std::vector<std::string> tmp_var_net;
        int cnt_var_net = 0;
        for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
          std::string tmp_str = "";         // building literal
          std::vector<std::string> tmp_var; // store all clauses
          int cnt_var = 0;
          int cnt_true = 0;
          // incoming
          if (SMTCell::ifEdgeIn(vCoord.getVname())) {
            for (int i : SMTCell::getEdgeIn(vCoord.getVname())) {
              tmp_str = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  SMTCell::getUdEdge(i)->getUdFromEdge()->getVname(),
                  vCoord.getVname());
              // make this into a class method
              switch (SMTCell::assignVar(tmp_str)) {
              case 1:
                tmp_var.push_back(tmp_str);
                cnt_var++;
                break;
              case 0:
                cnt_true++;
                break;
              }
            }
          }

          // outcoming
          if (SMTCell::ifEdgeOut(vCoord.getVname())) {
            for (int i : SMTCell::getEdgeOut(vCoord.getVname())) {
              tmp_str = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  vCoord.getVname(),
                  SMTCell::getUdEdge(i)->getUdToEdge()->getVname());
              // make this into a class method
              switch (SMTCell::assignVar(tmp_str)) {
              case 1:
                tmp_var.push_back(tmp_str);
                cnt_var++;
                break;
              case 0:
                cnt_true++;
                break;
              }
            }
          }

          // v-outcoming
          if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
            for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
              if (SMTCell::getVirtualEdge(i)->getPinName() ==
                  SMTCell::getNet(netIndex)->getSource_ofNet()) {
                tmp_str = fmt::format("N{}_E_{}_{}",
                                      SMTCell::getNet(netIndex)->getNetID(),
                                      vCoord.getVname(),
                                      SMTCell::getVirtualEdge(i)->getPinName());
                switch (SMTCell::assignVar(tmp_str)) {
                case 1:
                  tmp_var.push_back(tmp_str);
                  cnt_var++;
                  break;
                case 0:
                  cnt_true++;
                  break;
                }
              }
              for (int commodityIndex = 0;
                   commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
                   commodityIndex++) {
                if (SMTCell::getVirtualEdge(i)->getPinName() ==
                    SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex)) {
                  tmp_str = fmt::format(
                      "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      vCoord.getVname(),
                      SMTCell::getVirtualEdge(i)->getPinName());
                  switch (SMTCell::assignVar(tmp_str)) {
                  case 1:
                    tmp_var.push_back(tmp_str);
                    cnt_var++;
                    break;
                  case 0:
                    cnt_true++;
                    break;
                  }
                }
              }
            }
          }
          std::string tmp_enc = "";
          tmp_enc =
              fmt::format("C_N{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                          vCoord.getVname());
          if (cnt_true > 0) {
            SMTCell::setVar_wo_cnt(tmp_enc, 0);
            cnt_true_net++;
          } else if (cnt_var > 0) {
            SMTCell::setVar(tmp_enc, 0);
            tmp_var_net.push_back(tmp_enc);
            cnt_var_net++;
            SMTCell::writeConstraint(fmt::format("(assert (= {} (or", tmp_enc));
            SMTCell::cnt("l", 1);
            for (auto s : tmp_var) {
              SMTCell::writeConstraint(fmt::format(" {}", s));
              SMTCell::cnt("l", 1);
            }
            SMTCell::writeConstraint(")))\n");
            SMTCell::cnt("c", 1);
          }
        }
        if (cnt_true_net > 0) {
          fmt::print(
              "[ERROR] There exsits more than 2 nets sharing same vertex[{}]",
              vCoord.getVname());
          exit(-1);
        } else if (cnt_true_net == 1) {
          // remained net encode variables shoule be false
          for (auto s : tmp_var_net) {
            SMTCell::assignTrueVar(s, 0, true);
          }
        } else if (cnt_var_net > 0) {
          // at-most 1
          SMTCell::writeConstraint("(assert ((_ at-most 1)");
          for (auto s : tmp_var_net) {
            SMTCell::writeConstraint(fmt::format(" {}", s));
            SMTCell::cnt("l", 1);
          }
          SMTCell::writeConstraint("))\n");
          SMTCell::cnt("c", 1);
        }
      }
    }
  }

  // line 6487
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    std::string tmp_str = "";
    std::vector<std::string> tmp_var;
    int cnt_var = 0;
    int cnt_true = 0;
    for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }
      for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet vCoord = {metal, row, col};
          if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
            for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
              if (SMTCell::getVirtualEdge(i)->getPinName() ==
                  SMTCell::getNet(netIndex)->getSource_ofNet()) {
                tmp_str = fmt::format("N{}_E_{}_{}",
                                      SMTCell::getNet(netIndex)->getNetID(),
                                      vCoord.getVname(),
                                      SMTCell::getVirtualEdge(i)->getPinName());
                switch (SMTCell::assignVar(tmp_str)) {
                case 1:
                  tmp_var.push_back(tmp_str);
                  cnt_var++;
                  break;
                case 0:
                  cnt_true++;
                  break;
                }
              }
            }
          }
        }
      }
    }
    if (cnt_true > 0) {
      if (cnt_true > 1) {
        fmt::print("[ERROR] # of true pin in Net{}] exceeds one!!\n",
                   SMTCell::getNet(netIndex)->getNetID());
        exit(-1);
      } else {
        // if # of true variables is one, then remained variables should be
        // false
        for (auto s : tmp_var) {
          SMTCell::assignTrueVar(s, 0, true);
        }
      }
    }
    // true-assigned variable is not included in terms
    else {
      if (cnt_var == 1) {
        SMTCell::assignTrueVar(tmp_var[0], 1, true);
        SMTCell::setVar_wo_cnt(tmp_var[0], 0);
      } else if (cnt_var > 0) {
        // at-most 1
        SMTCell::writeConstraint("(assert ((_ at-most 1)");
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 1);
        // at-least 1
        SMTCell::writeConstraint("(assert ((_ at-least 1)");
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 1);
      }
    }
  }

  // line 6563
  // tmp_str.clear();
  // tmp_var.clear();
  // cnt_var = 0;
  // cnt_true = 0;
  std::string tmp_str;
  std::vector<std::string> tmp_var;
  int cnt_var = 0;
  int cnt_true = 0;
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }
      for (int row = 0; row <= SMTCell::getLastRowIdx(); row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet vCoord = {metal, row, col};
          if (SMTCell::ifVEdgeOut(vCoord.getVname())) {
            for (int i : SMTCell::getVEdgeOut(vCoord.getVname())) {
              for (int commodityIndex = 0;
                   commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
                   commodityIndex++) {
                if (SMTCell::getVirtualEdge(i)->getPinName() ==
                        SMTCell::getNet(netIndex)->getSinks_inNet(
                            commodityIndex) &&
                    SMTCell::getVirtualEdge(i)->getPinName() == Pin::keySON) {
                  tmp_str = fmt::format(
                      "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      vCoord.getVname(),
                      SMTCell::getVirtualEdge(i)->getPinName());
                  switch (SMTCell::assignVar(tmp_str)) {
                  case 1:
                    tmp_var.push_back(tmp_str);
                    cnt_var++;
                    break;
                  case 0:
                    cnt_true++;
                    break;
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // line 6593
  if (cnt_true > 0) {
    if (cnt_true > SMTCell::getOuterPinCnt()) {
      fmt::print("[ERROR] # of true pinson exceeds {}!!\n",
                 SMTCell::getOuterPinCnt());
      exit(-1);
    } else if (cnt_true == SMTCell::getOuterPinCnt()) {
      // # if # of true variables is the same as # of outerpins, then
      // remained variables should be false
      for (auto s : tmp_var) {
        switch (SMTCell::assignVar(s)) {
        case 1:
          SMTCell::assignTrueVar(s, 0, true);
          break;
        case 0:
          break;
        }
      }
    } else {
      // # at-most $numOuterPins-cnt_true
      SMTCell::writeConstraint(fmt::format(
          "(assert ((_ at-most {})", (SMTCell::getOuterPinCnt() - cnt_true)));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
      // at-least numOuterPins-cnt_true
      SMTCell::writeConstraint(fmt::format(
          "(assert ((_ at-least {})", (SMTCell::getOuterPinCnt() - cnt_true)));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
    }
  }
  // true-assigned variable is not included in terms
  else {
    if (cnt_var > 0) {
      // at-most numOuterPins
      SMTCell::writeConstraint(
          fmt::format("(assert ((_ at-most {})", SMTCell::getOuterPinCnt()));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
      // at-least numOuterPins
      SMTCell::writeConstraint(
          fmt::format("(assert ((_ at-least {})", SMTCell::getOuterPinCnt()));
      for (auto s : tmp_var) {
        SMTCell::writeConstraint(fmt::format(" {}", s));
        SMTCell::cnt("l", 1);
      }
      SMTCell::writeConstraint("))\n");
      SMTCell::cnt("c", 1);
    }
  }
  std::cout << "has been written.\n";
}

/**
 * Edge Assignment:
 * Associate Edge assignment with Nets
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void FlowWriter::write_edge_assignment(FILE *fp) {
  SMTCell::writeConstraint(";3. Edge assignment for each edge for every net\n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int udeIndex = 0; udeIndex < SMTCell::getUdEdgeCnt(); udeIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string tmp_com = "";
        tmp_com = fmt::format(
            "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            commodityIndex,
            SMTCell::getUdEdge(udeIndex)->getUdFromEdge()->getVname(),
            SMTCell::getUdEdge(udeIndex)->getUdToEdge()->getVname());
        std::string tmp_net = "";
        tmp_net = fmt::format(
            "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            SMTCell::getUdEdge(udeIndex)->getUdFromEdge()->getVname(),
            SMTCell::getUdEdge(udeIndex)->getUdToEdge()->getVname());
        if (!SMTCell::ifAssigned(tmp_com) && !SMTCell::ifAssigned(tmp_net)) {
          SMTCell::setVar(tmp_net, 2);
          SMTCell::setVar(tmp_net, 2);
          SMTCell::writeConstraint(
              fmt::format("(assert (ite (= {} true) (= {} true) (= 1 1)))\n",
                          tmp_com, tmp_net));
          SMTCell::cnt("l", 1);
          SMTCell::cnt("l", 1);
          SMTCell::cnt("c", 1);
        } else if (SMTCell::ifAssigned(tmp_com) &&
                   SMTCell::getAssigned(tmp_com) == 1) {
          SMTCell::assignTrueVar(tmp_net, 1, true);
          SMTCell::setVar_wo_cnt(tmp_net, 2);
        }
      }
    }
    for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
         vEdgeIndex++) {
      int isInNet = 0;
      // ignoring $virtualEdges[$vEdgeIndex][2] =~ /^pin/ since this is always
      // a pin name
      if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
          SMTCell::getNet(netIndex)->getSource_ofNet()) {
        isInNet = 1;
      }
      if (isInNet == 1) {
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          std::string tmp_com = "";
          tmp_com = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
              SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
          std::string tmp_net = "";
          tmp_net =
              fmt::format("N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                          SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                          SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
          if (!SMTCell::ifAssigned(tmp_com) && !SMTCell::ifAssigned(tmp_net)) {
            SMTCell::setVar(tmp_net, 2);
            SMTCell::setVar(tmp_net, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert (ite (= {} true) (= {} true) (= 1 1)))\n",
                            tmp_com, tmp_net));
            SMTCell::cnt("l", 1);
            SMTCell::cnt("l", 1);
            SMTCell::cnt("c", 1);
          } else if (SMTCell::ifAssigned(tmp_com) &&
                     SMTCell::getAssigned(tmp_com) == 1) {
            SMTCell::assignTrueVar(tmp_net, 1, true);
            SMTCell::setVar_wo_cnt(tmp_net, 2);
          }
        }
      }
      isInNet = 0;
      for (int i = 0; i < SMTCell::getNet(netIndex)->getNumSinks(); i++) {
        if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
            SMTCell::getNet(netIndex)->getSinks_inNet(i)) {
          isInNet = 1;
        }
      }
      if (isInNet == 1) {
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex)) {
            std::string tmp_com = "";
            tmp_com = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
            std::string tmp_net = "";
            tmp_net = fmt::format(
                "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
            if (!SMTCell::ifAssigned(tmp_com) &&
                !SMTCell::ifAssigned(tmp_net)) {
              SMTCell::setVar(tmp_net, 2);
              SMTCell::setVar(tmp_net, 2);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (= {} true) (= {} true) (= 1 1)))\n", tmp_com,
                  tmp_net));
              SMTCell::cnt("l", 1);
              SMTCell::cnt("l", 1);
              SMTCell::cnt("c", 1);
            } else if (SMTCell::ifAssigned(tmp_com) &&
                       SMTCell::getAssigned(tmp_com) == 1) {
              SMTCell::assignTrueVar(tmp_net, 1, true);
              SMTCell::setVar_wo_cnt(tmp_net, 2);
            }
          }
        }
      }
    }
  }
  std::cout << "has been written.\n";
  SMTCell::writeConstraint("\n");
}

/**
 * Edge Exclusiveness:
 * No duplication in usage of edges
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void FlowWriter::write_edge_exclusive(FILE *fp) {
  SMTCell::writeConstraint(
      ";4. Exclusiveness use of each edge + Metal segment assignment by "
      "using edge usage information\n");
  for (int udeIndex = 0; udeIndex < SMTCell::getUdEdgeCnt(); udeIndex++) {
    // tmp_str.clear();
    // tmp_var.clear();
    // cnt_var = 0;
    // cnt_true = 0;
    std::string tmp_str;
    std::vector<std::string> tmp_var;
    int cnt_var = 0;
    int cnt_true = 0;
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      tmp_str =
          fmt::format("N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                      SMTCell::getUdEdge(udeIndex)->getUdFromEdge()->getVname(),
                      SMTCell::getUdEdge(udeIndex)->getUdToEdge()->getVname());
      switch (SMTCell::assignVar(tmp_str)) {
      case 1:
        tmp_var.push_back(tmp_str);
        cnt_var++;
        break;
      case 0:
        cnt_true++;
        break;
      }
    }

    std::string tmp_str_metal = fmt::format(
        "M_{}_{}", SMTCell::getUdEdge(udeIndex)->getUdFromEdge()->getVname(),
        SMTCell::getUdEdge(udeIndex)->getUdToEdge()->getVname());

    if (cnt_true > 0) {
      SMTCell::assignTrueVar(tmp_str_metal, 1, true);
      SMTCell::setVar_wo_cnt(tmp_str_metal, 0);
    } else if (cnt_var > 0) {
      if (SMTCell::getAssigned(tmp_str_metal) == 0) {
        for (auto s : tmp_var) {
          SMTCell::assignTrueVar(s, 0, true);
        }
      } else {
        SMTCell::setVar(tmp_str_metal, 2);
        // # OR
        SMTCell::writeConstraint(
            fmt::format("(assert (= {} (or", tmp_str_metal));
        SMTCell::cnt("l", 1);
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint(")))\n");
        SMTCell::cnt("c", 1);
        // at-most 1
        SMTCell::writeConstraint("(assert ((_ at-most 1)");
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 1);
      }
    }
  }

  for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
       vEdgeIndex++) {
    // tmp_str.clear();
    // tmp_var.clear();
    // cnt_var = 0;
    // cnt_true = 0;
    std::string tmp_str;
    std::vector<std::string> tmp_var;
    int cnt_var = 0;
    int cnt_true = 0;

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      int isInNet = 0;
      // ignore regex for pin
      if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
          SMTCell::getNet(netIndex)->getSource_ofNet()) {
        isInNet = 1;
      }

      if (isInNet == 1) {
        tmp_str =
            fmt::format("N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                        SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                        SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
        switch (SMTCell::assignVar(tmp_str)) {
        case 1:
          tmp_var.push_back(tmp_str);
          cnt_var++;
          break;
        case 0:
          cnt_true++;
          break;
        }
      }

      isInNet = 0;
      for (int i = 0; i < SMTCell::getNet(netIndex)->getNumSinks(); i++) {
        if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() ==
            SMTCell::getNet(netIndex)->getSinks_inNet(i)) {
          isInNet = 1;
        }
      }

      if (isInNet == 1) {
        tmp_str =
            fmt::format("N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                        SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                        SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
        switch (SMTCell::assignVar(tmp_str)) {
        case 1:
          tmp_var.push_back(tmp_str);
          cnt_var++;
          break;
        case 0:
          cnt_true++;
          break;
        }
      }
    }

    std::string tmp_str_metal =
        fmt::format("M_{}_{}", SMTCell::getVirtualEdge(vEdgeIndex)->getVName(),
                    SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());

    if (cnt_true > 0) {
      SMTCell::assignTrueVar(tmp_str_metal, 1, true);
      SMTCell::setVar_wo_cnt(tmp_str_metal, 0);
    } else if (cnt_var > 0) {
      if (SMTCell::getAssigned(tmp_str_metal) == 0) {
        for (auto s : tmp_var) {
          SMTCell::assignTrueVar(s, 0, true);
        }
      } else if (cnt_var == 1) {
        SMTCell::setVar(tmp_str_metal, 2);
        SMTCell::writeConstraint(
            fmt::format("(assert (= {} {}))\n", tmp_var[0], tmp_str_metal));
      } else {
        SMTCell::setVar(tmp_str_metal, 2);
        // # OR
        SMTCell::writeConstraint(
            fmt::format("(assert (= {} (or", tmp_str_metal));
        SMTCell::cnt("l", 1);
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint(")))\n");
        SMTCell::cnt("c", 1);
        // at-most 1
        SMTCell::writeConstraint("(assert ((_ at-most 1)");
        for (auto s : tmp_var) {
          SMTCell::writeConstraint(fmt::format(" {}", s));
          SMTCell::cnt("l", 1);
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 1);
      }
    }
  }
  std::cout << "has been written.\n";
}

/**
 * External Net Consistency accross Metal Layers:
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void FlowWriter::write_net_consistency() {
  if (SMTCell::getNumMetalLayer() > 2) {
    std::map<std::string, int> h_tmp;
    for (auto en : SMTCell::getExtNet()) {
      int netIndex = SMTCell::getNetIdx(std::to_string(en.first));
      int metal = 3;
      int step = SMTCell::getMetalThreeStep();
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        std::string tmp_net_col_name = fmt::format("{}_{}", en.first, col);
        if (h_tmp.find(tmp_net_col_name) == h_tmp.end()) {
          for (int row_i = 0; row_i <= SMTCell::getNumTrackH() - 3; row_i++) {
            // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
            //   continue;
            // }
            Triplet *vCoord_i = new Triplet(metal, row_i, col);
            if (SMTCell::ifVEdgeOut(vCoord_i->getVname())) {
              for (int i : SMTCell::getVEdgeOut(vCoord_i->getVname())) {
                for (int commodityIndex = 0;
                     commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
                     commodityIndex++) {
                  if (SMTCell::getVirtualEdge(i)->getPinName() ==
                          SMTCell::getNet(netIndex)->getSinks_inNet(
                              commodityIndex) &&
                      SMTCell::getVirtualEdge(i)->getPinName() == Pin::keySON) {
                    if (h_tmp.find(tmp_net_col_name) == h_tmp.end()) {
                      h_tmp[tmp_net_col_name] = 1;
                    }

                    std::string tmp_str_e = fmt::format(
                        "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                        vCoord_i->getVname(),
                        SMTCell::getVirtualEdge(i)->getPinName());

                    if (!SMTCell::ifAssigned(tmp_str_e) ||
                        SMTCell::ifAssignedTrue(tmp_str_e)) {
                      for (int row_j = 0; row_j <= SMTCell::getNumTrackH() - 3;
                           row_j++) {
                        Triplet *vCoord_j = new Triplet(metal, row_j, col);
                        std::string tmp_str = "";
                        std::vector<std::string> tmp_var_self;
                        std::vector<std::string> tmp_var_self_c;
                        int cnt_var_self = 0;
                        int cnt_var_self_c = 0;
                        int cnt_true_self = 0;
                        int cnt_true_self_c = 0;

                        if (SMTCell::ifVertex((*vCoord_j)) &&
                            SMTCell::getVertex((*vCoord_j))
                                ->getBackADJ()
                                ->ifValid()) {
                          tmp_str =
                              fmt::format("N{}_E_{}_{}",
                                          SMTCell::getNet(netIndex)->getNetID(),
                                          vCoord_j->getVname(),
                                          SMTCell::getVertex((*vCoord_j))
                                              ->getBackADJ()
                                              ->getVname());
                          if (!SMTCell::ifAssigned(tmp_str)) {
                            tmp_var_self.push_back(tmp_str);
                            SMTCell::setVar(tmp_str, 2);
                            cnt_var_self++;
                          } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                            SMTCell::setVar_wo_cnt(tmp_str, 2);
                            cnt_true_self++;
                          }
                          // potential bug: nested for loop with same index
                          // name?
                          for (int commodityIndex = 0;
                               commodityIndex <
                               SMTCell::getNet(netIndex)->getNumSinks();
                               commodityIndex++) {
                            tmp_str = fmt::format(
                                "N{}_C{}_E_{}_{}",
                                SMTCell::getNet(netIndex)->getNetID(),
                                commodityIndex, vCoord_j->getVname(),
                                SMTCell::getVertex((*vCoord_j))
                                    ->getBackADJ()
                                    ->getVname());
                            if (!SMTCell::ifAssigned(tmp_str)) {
                              tmp_var_self_c.push_back(tmp_str);
                              SMTCell::setVar(tmp_str, 2);
                              cnt_var_self_c++;
                            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                              SMTCell::setVar_wo_cnt(tmp_str, 2);
                              cnt_true_self_c++;
                            }
                          }
                          if (!SMTCell::ifAssigned(tmp_str_e)) {
                            SMTCell::setVar(tmp_str_e, 2);
                            SMTCell::writeConstraint(
                                fmt::format("(assert (ite (and (= "
                                            "N{}_M2_TRACK false) (= {} true)",
                                            en.first, tmp_str_e));
                            SMTCell::cnt("l", 3);
                          } else if (SMTCell::ifAssignedTrue(tmp_str_e)) {
                            SMTCell::setVar_wo_cnt(tmp_str_e, 0);
                            SMTCell::writeConstraint(fmt::format(
                                "(assert (ite (and (= N{}_M2_TRACK false)",
                                en.first));
                          }

                          SMTCell::writeConstraint(
                              fmt::format(" (= {} true)", tmp_var_self[0]));

                          for (int i = 0; i < tmp_var_self_c.size(); i++) {
                            SMTCell::writeConstraint(fmt::format(
                                " (= {} false)", tmp_var_self_c[i]));
                            SMTCell::cnt("l", 3);
                          }

                          SMTCell::writeConstraint(") ((_ at-least 1)");

                          std::vector<std::string> tmp_var_com;
                          int cnt_var_com = 0;
                          int cnt_true_com = 0;

                          Triplet *vCoord_k =
                              new Triplet(metal, row_j + 1, col);

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getBackADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex, vCoord_k->getVname(),
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getBackADJ()
                                      ->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getDownADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex,
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getDownADJ()
                                      ->getVname(),
                                  vCoord_k->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getUpADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex, vCoord_k->getVname(),
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getUpADJ()
                                      ->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (cnt_true_com == 0) {
                            if (cnt_var_com == 1) {
                              for (int m = 0; m < tmp_var_com.size(); m++) {
                                SMTCell::writeConstraint(
                                    fmt::format(" {}", tmp_var_com[m]));
                                SMTCell::cnt("l", 3);
                              }
                            } else if (cnt_var_com >= 1) {
                              SMTCell::writeConstraint(" (or");
                              for (int m = 0; m < tmp_var_com.size(); m++) {
                                SMTCell::writeConstraint(
                                    fmt::format(" {}", tmp_var_com[m]));
                                SMTCell::cnt("l", 3);
                              }
                              SMTCell::writeConstraint(")");
                            }
                          }

                          for (int row_k = row_j + 1;
                               row_k <= SMTCell::getNumTrackH() - 3; row_k++) {
                            std::vector<std::string> tmp_var_net;
                            tmp_var_com.clear();
                            int cnt_var_net = 0;
                            cnt_var_com = 0;
                            int cnt_true_net = 0;
                            cnt_true_com = 0;
                            for (int j = 0; j <= row_k - row_j - 1; j++) {
                              Triplet *vCoord_j =
                                  new Triplet(metal, (row_j + 1 + j), col);
                              if (SMTCell::ifVertex((*vCoord_j)) &&
                                  SMTCell::getVertex((*vCoord_j))
                                      ->getBackADJ()
                                      ->ifValid()) {
                                tmp_str = fmt::format(
                                    "N{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    vCoord_j->getVname(),
                                    SMTCell::getVertex((*vCoord_j))
                                        ->getBackADJ()
                                        ->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_net.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_net++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_net++;
                                }
                              }
                            }

                            vCoord_k = new Triplet(metal, row_k + 1, col);

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getBackADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex, vCoord_k->getVname(),
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getBackADJ()
                                        ->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getDownADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex,
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getDownADJ()
                                        ->getVname(),
                                    vCoord_k->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getUpADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex, vCoord_k->getVname(),
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getUpADJ()
                                        ->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (cnt_true_com == 0) {
                              if (cnt_var_com == 1) {
                                for (int m = 0; m < tmp_var_com.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" (and {}", tmp_var_com[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                for (int m = 0; m < tmp_var_net.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_net[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                              } else if (cnt_var_com >= 1) {
                                SMTCell::writeConstraint(" (and (or");
                                for (int m = 0; m < tmp_var_com.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_com[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                                for (int m = 0; m < tmp_var_net.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_net[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                              }
                            }
                          }

                          tmp_var_com.clear();
                          cnt_var_com = 0;
                          cnt_true_com = 0;

                          vCoord_k = new Triplet(metal, row_j, col);

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getFrontADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex,
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getFrontADJ()
                                      ->getVname(),
                                  vCoord_k->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getDownADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex,
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getDownADJ()
                                      ->getVname(),
                                  vCoord_k->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (SMTCell::ifVertex((*vCoord_k)) &&
                              SMTCell::getVertex((*vCoord_k))
                                  ->getUpADJ()
                                  ->ifValid()) {
                            for (int commodityIndex = 0;
                                 commodityIndex <
                                 SMTCell::getNet(netIndex)->getNumSinks();
                                 commodityIndex++) {
                              tmp_str = fmt::format(
                                  "N{}_C{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  commodityIndex, vCoord_k->getVname(),
                                  SMTCell::getVertex((*vCoord_k))
                                      ->getUpADJ()
                                      ->getVname());
                              if (!SMTCell::ifAssigned(tmp_str)) {
                                tmp_var_com.push_back(tmp_str);
                                SMTCell::setVar(tmp_str, 2);
                                cnt_var_com++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                SMTCell::setVar_wo_cnt(tmp_str, 2);
                                cnt_true_com++;
                              }
                            }
                          }

                          if (cnt_true_com == 0) {
                            if (cnt_var_com == 1) {
                              for (int m = 0; m < tmp_var_com.size(); m++) {
                                SMTCell::writeConstraint(
                                    fmt::format(" {}", tmp_var_com[m]));
                                SMTCell::cnt("l", 3);
                              }
                            } else if (cnt_var_com >= 1) {
                              SMTCell::writeConstraint(" (or");
                              for (int m = 0; m < tmp_var_com.size(); m++) {
                                SMTCell::writeConstraint(
                                    fmt::format(" {}", tmp_var_com[m]));
                                SMTCell::cnt("l", 3);
                              }
                              SMTCell::writeConstraint(")");
                            }
                          }

                          for (int row_k = 0; row_k <= row_j - 1; row_k++) {
                            std::vector<std::string> tmp_var_net;
                            tmp_var_com.clear();
                            int cnt_var_net = 0;
                            cnt_var_com = 0;
                            int cnt_true_net = 0;
                            cnt_true_com = 0;
                            for (int j = 0; j <= row_k; j++) {
                              Triplet *vCoord_j =
                                  new Triplet(metal, (row_j - j), col);
                              if (SMTCell::ifVertex((*vCoord_j)) &&
                                  SMTCell::getVertex((*vCoord_j))
                                      ->getFrontADJ()
                                      ->ifValid()) {
                                tmp_str = fmt::format(
                                    "N{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    SMTCell::getVertex((*vCoord_j))
                                        ->getFrontADJ()
                                        ->getVname(),
                                    vCoord_j->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_net.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_net++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_net++;
                                }
                              }
                            }

                            vCoord_k =
                                new Triplet(metal, row_j - row_k - 1, col);

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getFrontADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex,
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getFrontADJ()
                                        ->getVname(),
                                    vCoord_k->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getDownADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex,
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getDownADJ()
                                        ->getVname(),
                                    vCoord_k->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (SMTCell::ifVertex((*vCoord_k)) &&
                                SMTCell::getVertex((*vCoord_k))
                                    ->getUpADJ()
                                    ->ifValid()) {
                              for (int commodityIndex = 0;
                                   commodityIndex <
                                   SMTCell::getNet(netIndex)->getNumSinks();
                                   commodityIndex++) {
                                tmp_str = fmt::format(
                                    "N{}_C{}_E_{}_{}",
                                    SMTCell::getNet(netIndex)->getNetID(),
                                    commodityIndex, vCoord_k->getVname(),
                                    SMTCell::getVertex((*vCoord_k))
                                        ->getUpADJ()
                                        ->getVname());
                                if (!SMTCell::ifAssigned(tmp_str)) {
                                  tmp_var_com.push_back(tmp_str);
                                  SMTCell::setVar(tmp_str, 2);
                                  cnt_var_com++;
                                } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                                  SMTCell::setVar_wo_cnt(tmp_str, 2);
                                  cnt_true_com++;
                                }
                              }
                            }

                            if (cnt_true_com == 0) {
                              if (cnt_var_com == 1) {
                                for (int m = 0; m < tmp_var_com.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" (and {}", tmp_var_com[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                for (int m = 0; m < tmp_var_net.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_net[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                              } else if (cnt_var_com >= 1) {
                                SMTCell::writeConstraint(" (and (or");
                                for (int m = 0; m < tmp_var_com.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_com[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                                for (int m = 0; m < tmp_var_net.size(); m++) {
                                  SMTCell::writeConstraint(
                                      fmt::format(" {}", tmp_var_net[m]));
                                  SMTCell::cnt("l", 3);
                                }
                                SMTCell::writeConstraint(")");
                              }
                            }
                          }
                          SMTCell::writeConstraint(") (= true true)))\n");
                          SMTCell::cnt("c", 3);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  fmt::print(" has been written\n");
}