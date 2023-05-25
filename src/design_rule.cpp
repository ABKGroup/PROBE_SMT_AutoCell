#include "design_rule.hpp"
#include "SMTCell.hpp"

namespace bmp = boost::multiprecision;
/**
 * Geometric Variables (GV):
 * Indicator for end of metal
 * 
 * @param   void
 *
 * @return  void
 */
void DesignRuleWriter::write_geometric_variables() {
  SMTCell::writeConstraint(";6. Geometry variables for Left (GL), Right "
                           "(GR), Front (GF), and Back (GB) directions\n");
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  SMTCell::writeConstraint(
      ";6-A. Geometry variables for Left-tip on each vertex\n");
  DesignRuleWriter::write_geometric_variables_left_tip_helper();
  SMTCell::writeConstraint("\n");

  // line 7006
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  SMTCell::writeConstraint(
      ";6-B. Geometry variables for Right-tip on each vertex\n");
  DesignRuleWriter::write_geometric_variables_right_tip_helper();
  SMTCell::writeConstraint("\n");

  // line 7123
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  SMTCell::writeConstraint(
      ";6-C. Geometry variables for Front-tip on each vertex\n");
  // # At the top-most metal layer, only vias exist.
  DesignRuleWriter::write_geometric_variables_front_tip_helper();
  SMTCell::writeConstraint("\n");

  // line 7241
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  SMTCell::writeConstraint(
      ";6-D. Geometry variables for Back-tip on each vertex\n");
  DesignRuleWriter::write_geometric_variables_back_tip_helper();
  SMTCell::writeConstraint("\n");
  std::cout << "have been written.\n";
}

void DesignRuleWriter::write_geometric_variables_left_tip_helper() {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal % 2 == 1) {
      continue;
    } else {
      int step = 0;
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
          Triplet *vCoord = new Triplet(metal, row, col);

          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }

          std::string tmp_g = fmt::format("GL_V_{}", vCoord->getVname());
          std::string tmp_m1 = "";

          if (SMTCell::getVertex((*vCoord))->getLeftADJ()->ifValid()) {
            tmp_m1 = fmt::format(
                "M_{}_{}",
                SMTCell::getVertex((*vCoord))->getLeftADJ()->getVname(),
                vCoord->getVname());
          } else {
            tmp_m1 = fmt::format("M_LeftEnd_{}", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m1, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert ((_ at-most 1) {} {}))\n", tmp_g, tmp_m1));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_m1) &&
                     SMTCell::getAssigned(tmp_m1) == 1) {
            if (!SMTCell::ifAssigned(tmp_g)) {
              SMTCell::assignTrueVar(tmp_g, 0, false);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::assignTrueVar(tmp_m1, 0, false);
            }
          }
          std::string tmp_m2 = "";
          if (SMTCell::getVertex((*vCoord))->getRightADJ()->ifValid()) {
            tmp_m2 = fmt::format(
                "M_{}_{}", vCoord->getVname(),
                SMTCell::getVertex((*vCoord))->getRightADJ()->getVname());
          } else {
            tmp_m2 = fmt::format("M_{}_RightEnd", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m2, 2);
            SMTCell::writeConstraint(fmt::format(
                "(assert (ite (= {} true) (= {} true) (= true true)))\n", tmp_g,
                tmp_m2));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::assignTrueVar(tmp_m2, 1, false);
              SMTCell::setVar_wo_cnt(tmp_m2, 1);
            }
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::setVar(tmp_g, 6);
              SMTCell::setVar(tmp_m1, 2);
              SMTCell::setVar(tmp_m2, 2);
              SMTCell::writeConstraint(
                  fmt::format("(assert (ite (= (or {} {}) false) (= {} "
                              "false) (= true true)))\n",
                              tmp_g, tmp_m1, tmp_m2));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 0) {
            if (SMTCell::ifAssigned(tmp_m1) &&
                SMTCell::getAssigned(tmp_m1) == 0) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::assignTrueVar(tmp_m2, 1, false);
                SMTCell::setVar_wo_cnt(tmp_m2, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_m1)) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_m1, tmp_m2));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          } else if (SMTCell::ifAssigned(tmp_m1) &&
                     SMTCell::getAssigned(tmp_m1) == 0) {
            if (SMTCell::ifAssigned(tmp_g) &&
                SMTCell::getAssigned(tmp_g) == 0) {
              // need review, DSY
              if (!SMTCell::ifAssigned(tmp_g)) {
                SMTCell::assignTrueVar(tmp_g, 1, false);
                SMTCell::setVar_wo_cnt(tmp_g, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_g)) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::setVar(tmp_g, 2);
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_g, tmp_m2));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

void DesignRuleWriter::write_geometric_variables_right_tip_helper() {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal % 2 == 1) {
      continue;
    } else {
      int step = 0;
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
          Triplet *vCoord = new Triplet(metal, row, col);

          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }

          std::string tmp_g = fmt::format("GR_V_{}", vCoord->getVname());
          std::string tmp_m1 = "";
          if (SMTCell::getVertex((*vCoord))->getLeftADJ()->ifValid()) {
            tmp_m1 = fmt::format(
                "M_{}_{}",
                SMTCell::getVertex((*vCoord))->getLeftADJ()->getVname(),
                vCoord->getVname());
          } else {
            tmp_m1 = fmt::format("M_LeftEnd_{}", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m1, 2);
            SMTCell::writeConstraint(fmt::format(
                "(assert (ite (= {} true) (= {} true) (= true true)))\n", tmp_g,
                tmp_m1));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::assignTrueVar(tmp_m1, 1, false);
              SMTCell::setVar_wo_cnt(tmp_m1, 1);
            }
          }
          std::string tmp_m2 = "";
          if (SMTCell::getVertex((*vCoord))->getRightADJ()->ifValid()) {
            tmp_m2 = fmt::format(
                "M_{}_{}", vCoord->getVname(),
                SMTCell::getVertex((*vCoord))->getRightADJ()->getVname());
          } else {
            tmp_m2 = fmt::format("M_{}_RightEnd", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m2, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert ((_ at-most 1) {} {}))\n", tmp_g, tmp_m2));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_m2) &&
                     SMTCell::getAssigned(tmp_m2) == 1) {
            if (!SMTCell::ifAssigned(tmp_g)) {
              SMTCell::assignTrueVar(tmp_g, 0, false);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::assignTrueVar(tmp_m2, 0, false);
            }
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::setVar(tmp_g, 6);
              SMTCell::setVar(tmp_m1, 2);
              SMTCell::setVar(tmp_m2, 2);
              SMTCell::writeConstraint(
                  fmt::format("(assert (ite (= (or {} {}) false) (= {} "
                              "false) (= true true)))\n",
                              tmp_g, tmp_m2, tmp_m1));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 0) {
            if (SMTCell::ifAssigned(tmp_m2) &&
                SMTCell::getAssigned(tmp_m2) == 0) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::assignTrueVar(tmp_m1, 1, false);
                SMTCell::setVar_wo_cnt(tmp_m1, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_m2)) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_m2, tmp_m1));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          } else if (SMTCell::ifAssigned(tmp_m2) &&
                     SMTCell::getAssigned(tmp_m2) == 0) {
            if (SMTCell::ifAssigned(tmp_g) &&
                SMTCell::getAssigned(tmp_g) == 0) {
              // need review, DSY
              if (!SMTCell::ifAssigned(tmp_g)) {
                SMTCell::assignTrueVar(tmp_g, 1, false);
                SMTCell::setVar_wo_cnt(tmp_g, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_g)) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::setVar(tmp_g, 2);
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_g, tmp_m1));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

void DesignRuleWriter::write_geometric_variables_front_tip_helper() {
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal % 2 == 1) {
      int step = 0;
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
          if (metal == 1 && col % (2 * step) == step) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }

          std::string tmp_g = fmt::format("GF_V_{}", vCoord->getVname());
          std::string tmp_m1 = "";
          if (SMTCell::getVertex((*vCoord))->getFrontADJ()->ifValid()) {
            tmp_m1 = fmt::format(
                "M_{}_{}",
                SMTCell::getVertex((*vCoord))->getFrontADJ()->getVname(),
                vCoord->getVname());
          } else {
            tmp_m1 = fmt::format("M_FrontEnd_{}", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m1, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert ((_ at-most 1) {} {}))\n", tmp_g, tmp_m1));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_m1) &&
                     SMTCell::getAssigned(tmp_m1) == 1) {
            if (!SMTCell::ifAssigned(tmp_g)) {
              SMTCell::assignTrueVar(tmp_g, 0, false);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::assignTrueVar(tmp_m1, 0, false);
            }
          }
          std::string tmp_m2 = "";
          if (SMTCell::getVertex((*vCoord))->getBackADJ()->ifValid()) {
            tmp_m2 = fmt::format(
                "M_{}_{}", vCoord->getVname(),
                SMTCell::getVertex((*vCoord))->getBackADJ()->getVname());
          } else {
            tmp_m2 = fmt::format("M_{}_BackEnd", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m2, 2);
            SMTCell::writeConstraint(fmt::format(
                "(assert (ite (= {} true) (= {} true) (= true true)))\n", tmp_g,
                tmp_m2));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::assignTrueVar(tmp_m2, 1, false);
              SMTCell::setVar_wo_cnt(tmp_m2, 1);
            }
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::setVar(tmp_g, 6);
              SMTCell::setVar(tmp_m1, 2);
              SMTCell::setVar(tmp_m2, 2);
              SMTCell::writeConstraint(
                  fmt::format("(assert (ite (= (or {} {}) false) (= {} "
                              "false) (= true true)))\n",
                              tmp_g, tmp_m1, tmp_m2));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 0) {
            if (SMTCell::ifAssigned(tmp_m1) &&
                SMTCell::getAssigned(tmp_m1) == 0) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::assignTrueVar(tmp_m2, 1, false);
                SMTCell::setVar_wo_cnt(tmp_m2, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_m1)) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_m1, tmp_m2));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          } else if (SMTCell::ifAssigned(tmp_m1) &&
                     SMTCell::getAssigned(tmp_m1) == 0) {
            if (SMTCell::ifAssigned(tmp_g) &&
                SMTCell::getAssigned(tmp_g) == 0) {
              // need review, DSY
              if (!SMTCell::ifAssigned(tmp_g)) {
                SMTCell::assignTrueVar(tmp_g, 1, false);
                SMTCell::setVar_wo_cnt(tmp_g, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_g)) {
              if (!SMTCell::ifAssigned(tmp_m2)) {
                SMTCell::setVar(tmp_g, 2);
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_g, tmp_m2));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

void DesignRuleWriter::write_geometric_variables_back_tip_helper() {
  // # At the top-most metal layer, only vias exist.
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer(); metal++) {
    if (metal % 2 == 1) {
      int step = 0;
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
          if (metal == 1 && col % (2 * step) == step) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }

          std::string tmp_g = fmt::format("GB_V_{}", vCoord->getVname());
          std::string tmp_m1 = "";
          if (SMTCell::getVertex((*vCoord))->getFrontADJ()->ifValid()) {
            tmp_m1 = fmt::format(
                "M_{}_{}",
                SMTCell::getVertex((*vCoord))->getFrontADJ()->getVname(),
                vCoord->getVname());
          } else {
            tmp_m1 = fmt::format("M_FrontEnd_{}", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m1)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m1, 2);
            SMTCell::writeConstraint(fmt::format(
                "(assert (ite (= {} true) (= {} true) (= true true)))\n", tmp_g,
                tmp_m1));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::assignTrueVar(tmp_m1, 1, false);
              SMTCell::setVar_wo_cnt(tmp_m1, 1);
            }
          }
          std::string tmp_m2 = "";
          if (SMTCell::getVertex((*vCoord))->getBackADJ()->ifValid()) {
            tmp_m2 = fmt::format(
                "M_{}_{}", vCoord->getVname(),
                SMTCell::getVertex((*vCoord))->getBackADJ()->getVname());
          } else {
            tmp_m2 = fmt::format("M_{}_BackEnd", vCoord->getVname());
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            SMTCell::setVar(tmp_g, 6);
            SMTCell::setVar(tmp_m2, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert ((_ at-most 1) {} {}))\n", tmp_g, tmp_m2));
            SMTCell::cnt("l", 3);
            SMTCell::cnt("l", 3);
            SMTCell::cnt("c", 3);
          } else if (SMTCell::ifAssigned(tmp_m2) &&
                     SMTCell::getAssigned(tmp_m2) == 1) {
            if (!SMTCell::ifAssigned(tmp_g)) {
              SMTCell::assignTrueVar(tmp_g, 0, false);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 1) {
            if (!SMTCell::ifAssigned(tmp_m2)) {
              SMTCell::assignTrueVar(tmp_m2, 0, false);
            }
          }
          if (!SMTCell::ifAssigned(tmp_g) && !SMTCell::ifAssigned(tmp_m2)) {
            if (!SMTCell::ifAssigned(tmp_m1)) {
              SMTCell::setVar(tmp_g, 6);
              SMTCell::setVar(tmp_m2, 2);
              SMTCell::setVar(tmp_m1, 2);
              SMTCell::writeConstraint(
                  fmt::format("(assert (ite (= (or {} {}) false) (= {} "
                              "false) (= true true)))\n",
                              tmp_g, tmp_m2, tmp_m1));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          } else if (SMTCell::ifAssigned(tmp_g) &&
                     SMTCell::getAssigned(tmp_g) == 0) {
            if (SMTCell::ifAssigned(tmp_m2) &&
                SMTCell::getAssigned(tmp_m2) == 0) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::assignTrueVar(tmp_m1, 1, false);
                SMTCell::setVar_wo_cnt(tmp_m1, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_m2)) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::setVar(tmp_m2, 2);
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_m2, tmp_m1));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          } else if (SMTCell::ifAssigned(tmp_m2) &&
                     SMTCell::getAssigned(tmp_m2) == 0) {
            if (SMTCell::ifAssigned(tmp_g) &&
                SMTCell::getAssigned(tmp_g) == 0) {
              // need review, DSY
              if (!SMTCell::ifAssigned(tmp_g)) {
                SMTCell::assignTrueVar(tmp_g, 1, false);
                SMTCell::setVar_wo_cnt(tmp_g, 1);
              }
            } else if (!SMTCell::ifAssigned(tmp_g)) {
              if (!SMTCell::ifAssigned(tmp_m1)) {
                SMTCell::setVar(tmp_g, 2);
                SMTCell::setVar(tmp_m1, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (ite (= {} false) (= {} false) (= "
                                "true true)))\n",
                                tmp_g, tmp_m1));
                SMTCell::cnt("l", 3);
                SMTCell::cnt("l", 3);
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * Minimum Area Rule (MAR):
 * Enforces each disjoint metal segment should be larger than the
 * minimum manufacturable size.
 *
 * @note
 * Example: (MAR = 2) No Violation
 *     |    |    |
 * ====X====X====X
 *     |    |    |
 *
 * @param   PRL_Parameter   Distance in Graph
 * @param   doublePowerRail If using Double Power Rail
 *
 * @return  void
 */
void DesignRuleWriter::write_MAR_rule(int MAR_Parameter, int doublePowerRail) {

  SMTCell::writeConstraint(";7. Minimum Area Rule\n");

  if (MAR_Parameter == 0) {
    std::cout << "is disable\n";
    SMTCell::writeConstraint(";MAR is disable\n");
  } else {
    // # PRL Rule Enable /Disable
    // ### Minimum Area Rule to prevent from having small metal segment
    for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
      int step = 0;
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }
      if (metal % 2 == 0) {
        for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
          for (int col = 0; col <= SMTCell::getRealNumTrackV() - MAR_Parameter;
               col += step) {
            if (col % SMTCell::getMetalOneStep() != 0 &&
                col % SMTCell::getMetalThreeStep() != 0) {
              continue;
            }
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            for (int marIndex = 0; marIndex <= MAR_Parameter - 1; marIndex++) {
              int colNumber = col + marIndex * SMTCell::getMetalOneStep();
              Triplet *vCoord = new Triplet(metal, row, colNumber);

              // check if the vertex is valid
              if (!SMTCell::ifVertex((*vCoord))) {
                continue;
              }

              std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] MAR : more than one G Variables are "
                             "true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      } else {
        int MaxIndex = MAR_Parameter - 1;
        if (doublePowerRail == 1) {
          MaxIndex--;
        }
        if (metal == 1) {
          step = SMTCell::getMetalOneStep();
        } else if (metal >= 3) {
          step = SMTCell::getMetalThreeStep();
        } else {
          // # Metal 2 (M0)
          step = SMTCell::getGCDStep();
        }
        for (int row = 0; row <= SMTCell::getNumTrackH() - 3 - MaxIndex;
             row++) {
          for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
               col += step) {
            if (col % SMTCell::getMetalOneStep() != 0 &&
                col % SMTCell::getMetalThreeStep() != 0) {
              continue;
            }
            // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
            //   continue;
            // }
            int powerRailFlag = 0;
            int powerRailIndex = 0;
            Triplet *vCoord = new Triplet(metal, row, col);

            // check if the vertex is valid
            if (!SMTCell::ifVertex((*vCoord))) {
              continue;
            }

            int newRow = row;
            if (SMTCell::getVertex((*vCoord))->getBackADJ()->ifValid() ==
                    false ||
                ((doublePowerRail == 1) &&
                 ((newRow + 1) %
                      static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                  0) &&
                 (MAR_Parameter == 2))) {
              continue;
            }
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            for (int marIndex = 0; marIndex <= MAR_Parameter - 1; marIndex++) {
              powerRailIndex =
                  std::ceil(marIndex / (SMTCell::getTrackEachRow() + 2));
              if (doublePowerRail == 1 &&
                  newRow % static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                      0 &&
                  powerRailFlag < powerRailIndex) {
                powerRailFlag++;
                newRow++;
                continue;
              } else {
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                tmp_str = fmt::format("GB_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                newRow++;
                vCoord = SMTCell::getVertex((*vCoord))->getBackADJ();
                if (vCoord->ifValid() == false) {
                  break;
                }
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] MAR : more than one G Variables are "
                             "true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
    SMTCell::writeConstraint("\n");
    std::cout << "have been written.\n";
  }
}

/**
 * End-Of-Line Spacing Rule (EOL) rule:
 * Enforces the distance between each EOL of two metal segments that are coming
 * from opposite directions should be greater than the minimum spacing distance.
 *
 * @note
 * Example: (EOL = 2) No Violation
 * ----+----X====X===
 *     |    |    |
 * ====X----+----X===
 *     |    |    |
 * ----+----X====X===
 *
 * @param   EOL_Parameter   Distance in Graph
 * @param   doublePowerRail If using Double Power Rail
 *
 * @return  void
 */
void DesignRuleWriter::write_EOL_rule(int EOL_Parameter, int doublePowerRail) {
  SMTCell::writeConstraint(";8. Tip-to-Tip Spacing Rule\n");
  if (EOL_Parameter == 0) {
    std::cout << "is disable\n";
    SMTCell::writeConstraint(";EOL is disable\n");
  } else {
    // # PRL Rule Enable /Disable
    // ### Tip-to-Tip Spacing Rule to prevent from having too close metal
    // tips.
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    SMTCell::writeConstraint(
        ";8-A. from Right Tip to Left Tips for each vertex\n");
    DesignRuleWriter::write_EOL_RL_tip_helper(EOL_Parameter);
    SMTCell::writeConstraint("\n");

    // line 7738
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    SMTCell::writeConstraint(
        ";8-B. from Left Tip to Right Tips for each vertex\n");
    DesignRuleWriter::write_EOL_LR_tip_helper(EOL_Parameter);
    SMTCell::writeConstraint("\n");

    // line 7936
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    // #
    // ##### one Power Rail vertice has 2 times cost of other vertices.
    // #
    SMTCell::writeConstraint(
        ";8-C. from Back Tip to Front Tips for each vertex\n");
    DesignRuleWriter::write_EOL_BF_tip_helper(EOL_Parameter, doublePowerRail);
    SMTCell::writeConstraint("\n");

    // line 8182
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    SMTCell::writeConstraint(
        ";8-D. from Front Tip to Back Tips for each vertex\n");
    DesignRuleWriter::write_EOL_FB_tip_helper(EOL_Parameter, doublePowerRail);
    SMTCell::writeConstraint("\n");
    std::cout << "have been written.\n";
  }
}

/**
 * @note
 *                            ----+----X====X==== <--- BR Direction Checking
 *                                |    |    |
 *                            ▒▒▒▒X----+----X==== <--- R Direction Checking
 *                                |    |    |
 *                            ----+----X====X==== <--- FR Direction Checking
 */
void DesignRuleWriter::write_EOL_RL_tip_helper(int EOL_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) { // M2
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        // if (row == 0 || row == (SMTCell::getNumTrackH() - 3)) {
        //   // skip the EOL rule related with power rail
        // }
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 2 * step;
             col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);
          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }
          Triplet *vCoord_FR =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();
          // check if the vertex is valid
          if (SMTCell::ifVertex((*vCoord_FR))) {
            // Triplet Coord = Triplet(metal, row, col);
            // FR Direction Checking
            if (vCoord_FR->ifValid() && row != 0 && EOL_Parameter >= 2) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 2;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GL_V_{}", vCoord_FR->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 2)) {
                  vCoord_FR = SMTCell::getVertex((*vCoord_FR))->getRightADJ();
                  if (vCoord_FR->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
                  SMTCell::cnt("c", 3);
                }
              }
            }
          }

          // R Direction Checking
          Triplet *vCoord_R = SMTCell::getVertex((*vCoord))->getRightADJ();
          // check if the vertex is valid
          if (SMTCell::ifVertex((*vCoord_R))) {
            if (vCoord_R->ifValid()) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 1;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GL_V_{}", vCoord_R->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 1)) {
                  vCoord_R = SMTCell::getVertex((*vCoord_R))->getRightADJ();
                  if (vCoord_R->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
                  SMTCell::cnt("c", 3);
                }
              }
            }
          }

          // BR Direction Checking
          Triplet *vCoord_BR = SMTCell::getVertex((*vCoord))->getBackRightADJ();
          // check if the vertex is valid
          if (SMTCell::ifVertex((*vCoord_BR))) {
            if (vCoord_BR->ifValid() && row != (SMTCell::getNumTrackH() - 3) &&
                EOL_Parameter >= 2) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 2;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GL_V_{}", vCoord_BR->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 2)) {
                  vCoord_BR = SMTCell::getVertex((*vCoord_BR))->getRightADJ();
                  if (vCoord_BR->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
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

/**
 * @note
 *                            ====X====X----+---- <--- BL Direction Checking
 *                                |    |    |
 *                            ====X----+----X▒▒▒▒ <--- L Direction Checking
 *                                |    |    |
 *                            ====X====X----+---- <--- FL Direction Checking
 */
void DesignRuleWriter::write_EOL_LR_tip_helper(int EOL_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) {
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        if (row == 0 || row == (SMTCell::getNumTrackH() - 3)) {
          // skip the EOL rule related with power rail
        }
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);
          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }
          Triplet *vCoord_FL = SMTCell::getVertex((*vCoord))->getFrontLeftADJ();
          // check if the vertex is valid
          if (SMTCell::ifVertex((*vCoord_FL))) {
            // FL Direction Checking
            if (vCoord_FL->ifValid() && row != 0 && EOL_Parameter >= 2) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 2;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GR_V_{}", vCoord_FL->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 2)) {
                  vCoord_FL = SMTCell::getVertex((*vCoord_FL))->getLeftADJ();
                  if (vCoord_FL->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
                  SMTCell::cnt("c", 3);
                }
              }
            }
          }

          // L Direction Checking
          Triplet *vCoord_L = SMTCell::getVertex((*vCoord))->getLeftADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_L))) {
            if (vCoord_L->ifValid()) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());

              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 1;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GR_V_{}", vCoord_L->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 1)) {
                  vCoord_L = SMTCell::getVertex((*vCoord_L))->getLeftADJ();
                  if (vCoord_L->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
                  SMTCell::cnt("c", 3);
                }
              }
            }
          }

          // BL Direction Checking
          Triplet *vCoord_BL = SMTCell::getVertex((*vCoord))->getBackLeftADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_BL))) {
            if (vCoord_BL->ifValid() && row != (SMTCell::getNumTrackH() - 3) &&
                EOL_Parameter >= 2) {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              for (int eolIndex = 0; eolIndex <= EOL_Parameter - 2;
                   eolIndex++) {
                std::string tmp_str =
                    fmt::format("GR_V_{}", vCoord_BL->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                if (eolIndex != (EOL_Parameter - 2)) {
                  vCoord_BL = SMTCell::getVertex((*vCoord_BL))->getLeftADJ();
                  if (vCoord_BL->ifValid() == false) {
                    break;
                  }
                }
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                               "Variables are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
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

/**
 * @note
 *                                ║    ║    ║
 *                            ----X----X----X---- <--- B Direction Checking
 *                                ║    |    ║
 * BL Direction Checking ---> ----X----+----X---- <--- BR Direction Checking
 *                                |    |    |
 *                            ----+----X----+----
 *                                |    ▒    |
 */
void DesignRuleWriter::write_EOL_BF_tip_helper(int EOL_Parameter,
                                               int doublePowerRail) {
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 1) {
      for (int row = 0; row <= SMTCell::getNumTrackH() - 4; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          if (metal == 1 && SMTCell::ifSDCol(col)) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);
          // check if the vertex if valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }
          Triplet *vCoord_BL = SMTCell::getVertex((*vCoord))->getBackLeftADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_BL))) {
            // BL Direction Checking
            if (vCoord_BL->ifValid() && metal >= 2 && metal % 2 == 0 &&
                EOL_Parameter >= 2) {
              int newRow = row + 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 2) {
                // Skip the BR Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GB_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                for (int eolIndex = 1; eolIndex <= EOL_Parameter - 1;
                     eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GF_V_{}", vCoord_BL->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < (EOL_Parameter - 1)) {
                    vCoord_BL = SMTCell::getVertex((*vCoord_BL))->getBackADJ();
                    newRow++;
                    if (vCoord_BL->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
                    SMTCell::cnt("c", 3);
                  }
                }
              }
            }
          }

          // B Direction Checking
          Triplet *vCoord_B = SMTCell::getVertex((*vCoord))->getBackADJ();
          // check if the vertex is valid
          if (SMTCell::ifVertex((*vCoord_B))) {
            if (vCoord_B->ifValid()) {
              int newRow = row + 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 1) {
                // Skip the B Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GB_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                int eolMax = 0;
                if (metal == 1) {
                  eolMax = EOL_Parameter - 1;
                } else {
                  eolMax = EOL_Parameter;
                }

                for (int eolIndex = 1; eolIndex <= eolMax; eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GF_V_{}", vCoord_B->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < eolMax) {
                    vCoord_B = SMTCell::getVertex((*vCoord_B))->getBackADJ();
                    newRow++;
                    if (vCoord_B->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
                    SMTCell::cnt("c", 3);
                  }
                }
              }
            }
          }

          // BR Direction Checking
          Triplet *vCoord_BR = SMTCell::getVertex((*vCoord))->getBackRightADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_BR))) {
            if (vCoord_BR->ifValid() && metal >= 2 && metal % 2 == 0 &&
                EOL_Parameter >= 2) {
              int newRow = row + 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 2) {
                // Skip the BR Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GB_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                for (int eolIndex = 1; eolIndex <= EOL_Parameter - 1;
                     eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GF_V_{}", vCoord_BR->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < (EOL_Parameter - 1)) {
                    vCoord_BR = SMTCell::getVertex((*vCoord_BR))->getBackADJ();
                    newRow++;
                    if (vCoord_BR->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
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

/**
 * @note
 *                                |    ▒    |
 *                            ----+----X----+---- <--- F Direction Checking
 *                                |    |    |
 * FL Direction Checking ---> ----X----+----X---- <--- FR Direction Checking
 *                                ║    |    ║
 *                            ----X----X----X----
 *                                ║    ║    ║
 */
void DesignRuleWriter::write_EOL_FB_tip_helper(int EOL_Parameter,
                                               int doublePowerRail) {
  for (int metal = 1; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 1) {
      for (int row = 1; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          if (metal == 1 && SMTCell::ifSDCol(col)) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);
          // check if the vertex if valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }
          Triplet *vCoord_FL = SMTCell::getVertex((*vCoord))->getFrontLeftADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_FL))) {
            // FL Direction
            if (vCoord_FL->ifValid() && metal >= 2 && metal % 2 == 0 &&
                EOL_Parameter >= 2) {
              int newRow = row - 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 2) {
                // Skip the BR Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                for (int eolIndex = 1; eolIndex <= EOL_Parameter - 1;
                     eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GB_V_{}", vCoord_FL->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < (EOL_Parameter - 1)) {
                    vCoord_FL = SMTCell::getVertex((*vCoord_FL))->getFrontADJ();
                    newRow--;
                    if (vCoord_FL->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
                    SMTCell::cnt("c", 3);
                  }
                }
              }
            }
          }

          // F Direction Checking
          Triplet *vCoord_F = SMTCell::getVertex((*vCoord))->getFrontADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_F))) {
            if (vCoord_F->ifValid()) {
              int newRow = row - 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 1) {
                // Skip the B Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                int eolMax = 0;
                if (metal == 1) {
                  eolMax = EOL_Parameter - 1;
                } else {
                  eolMax = EOL_Parameter;
                }

                for (int eolIndex = 1; eolIndex <= eolMax; eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GB_V_{}", vCoord_F->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < eolMax) {
                    vCoord_F = SMTCell::getVertex((*vCoord_F))->getFrontADJ();
                    newRow--;
                    if (vCoord_F->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
                    SMTCell::cnt("c", 3);
                  }
                }
              }
            }
          }

          // FR Direction Checking
          Triplet *vCoord_FR =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();
          // check if the vertex if valid
          if (SMTCell::ifVertex((*vCoord_FR))) {
            if (vCoord_FR->ifValid() && metal >= 2 && metal % 2 == 0 &&
                EOL_Parameter >= 2) {
              int newRow = row - 1;
              if (doublePowerRail == 1 &&
                  (newRow %
                       static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                   0) &&
                  EOL_Parameter == 2) {
                // Skip the BR Direction
              } else {
                std::vector<std::string> tmp_var;
                int cnt_var = 0;
                int cnt_true = 0;
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }

                int powerRailFlag = 0;
                int powerRailIndex = 0;
                for (int eolIndex = 1; eolIndex <= EOL_Parameter - 1;
                     eolIndex++) {
                  powerRailIndex =
                      std::ceil(eolIndex / (SMTCell::getTrackEachRow() + 2));
                  if (doublePowerRail == 1 &&
                      (newRow %
                           static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                       0) &&
                      powerRailFlag < powerRailIndex) {
                    powerRailFlag++;
                    continue;
                  }
                  std::string tmp_str =
                      fmt::format("GB_V_{}", vCoord_FR->getVname());
                  if (!SMTCell::ifAssigned(tmp_str)) {
                    tmp_var.push_back(tmp_str);
                    SMTCell::setVar(tmp_str, 2);
                    cnt_var++;
                  } else if (SMTCell::ifAssigned(tmp_str) &&
                             SMTCell::getAssigned(tmp_str) == 1) {
                    SMTCell::setVar_wo_cnt(tmp_str, 0);
                    cnt_true++;
                  }
                  if (eolIndex < (EOL_Parameter - 1)) {
                    vCoord_FR = SMTCell::getVertex((*vCoord_FR))->getFrontADJ();
                    newRow--;
                    if (vCoord_FR->ifValid() == false) {
                      break;
                    }
                  }
                }
                if (cnt_true > 0) {
                  if (cnt_true > 1) {
                    std::cerr << "\n[ERROR] TIP2TIP : more than one G "
                                 "Variables are true!!!\n";
                    exit(1);
                  } else {
                    for (int i = 0; i < tmp_var.size(); i++) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                } else {
                  if (cnt_var > 1) {
                    SMTCell::writeConstraint(
                        fmt::format("(assert ((_ at-most 1)"));
                    for (auto s : tmp_var) {
                      SMTCell::writeConstraint(fmt::format(" {}", s));
                      SMTCell::cnt("l", 3);
                    }
                    SMTCell::writeConstraint(fmt::format("))\n"));
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

void DesignRuleWriter::write_VR_rule(float VR_Parameter, int doublePowerRail) {
  SMTCell::writeConstraint(";9. Via-to-Via Spacing Rule\n");
  if (VR_Parameter == 0) {
    std::cout << "is disable\n";
    SMTCell::writeConstraint(";VR is disable\n");
  } else {
    // # VR Rule Enable /Disable
    // ### Via-to-Via Spacing Rule to prevent from having too close vias and
    // stacked vias.
    // ### UNDIRECTED_EDGE [index] [Term1] [Term2] [Cost]
    // ### VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of adjacent
    // vertices]
    // ### ADJACENT_VERTICES [0:Left] [1:Right] [2:Front] [3:Back] [4:Up]
    // [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    // int maxDistRow = SMTCell::getNumTrackH() - 1;
    // int maxDistCol = SMTCell::getRealNumTrackV() - 1;
    DesignRuleWriter::write_VR_M1_helper(VR_Parameter, doublePowerRail);

    SMTCell::writeConstraint(
        fmt::format(";VIA Rule for M2~M4, VIA Rule is applied only for vias "
                    "between different nets\n"));

    DesignRuleWriter::write_VR_M2_M4_helper(VR_Parameter, doublePowerRail);
    std::cout << "have been written.\n";
  }
}

void DesignRuleWriter::write_VR_M1_helper(float VR_Parameter,
                                          int doublePowerRail) {
  for (int metal = 1; metal <= 1; metal++) {
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
        //   continue;
        // }
        if (row == SMTCell::getNumTrackH() - 3 &&
            col == SMTCell::getRealNumTrackV() - 1) {
          continue;
        }
        // Via-to-via Spacing Rule
        Triplet *vCoord = new Triplet(metal, row, col);

        // check if the vertex is valid
        if (!SMTCell::ifVertex((*vCoord))) {
          continue;
        }

        if (SMTCell::getVertex((*vCoord))
                ->getUpADJ()
                ->ifValid()) { // Up Neighbor, i.e., VIA from the vName vertex
          std::vector<std::string> tmp_var;
          int cnt_var = 0;
          int cnt_true = 0;
          std::string tmp_str = fmt::format(
              "M_{}_{}", vCoord->getVname(),
              SMTCell::getVertex((*vCoord))->getUpADJ()->getVname());
          if (!SMTCell::ifAssigned(tmp_str)) {
            tmp_var.push_back(tmp_str);
            SMTCell::setVar(tmp_str, 2);
            cnt_var++;
          } else if (SMTCell::ifAssignedTrue(tmp_str)) {
            SMTCell::setVar_wo_cnt(tmp_str, 0);
            cnt_true++;
          }

          for (int newRow = row; newRow <= SMTCell::getNumTrackH() - 3;
               newRow++) {
            for (int newCol = col; newCol <= SMTCell::getRealNumTrackV() - 1;
                 newCol += step) {
              int distCol = (newCol - col) / SMTCell::getMetalOneStep();
              int distRow = newRow - row;
              // Check power rail between newRow and row. (Double Power Rail
              // Rule Applying)
              if (doublePowerRail == 1 &&
                  floor(newRow / (SMTCell::getTrackEachRow() + 1)) !=
                      floor(row / (SMTCell::getTrackEachRow() + 1))) {
                distRow++;
              }

              if (newRow == row && newCol == col) { // Initial Value
                continue;
              }

              if ((distCol * distCol + distRow * distRow) >
                  (VR_Parameter * VR_Parameter)) { // Check the Via Distance
                break;
              }
              // Need to consider the Power rail distance by 2 like EOL rule
              Triplet *neighborCoord = new Triplet();
              std::memcpy(neighborCoord, vCoord, sizeof(Triplet));

              while (distCol > 0) {
                distCol--;
                neighborCoord =
                    SMTCell::getVertex((*neighborCoord))->getRightADJ();

                if (neighborCoord->ifValid() == false) {
                  break;
                }
              }

              if (SMTCell::ifVertex((*neighborCoord)) == false) {
                break;
              }

              int currentRow = row;
              int FlagforSecond = 0;
              while (distRow > 0) {
                distRow--;
                currentRow++;
                // Double Power Rail Effective Flag Code
                if (doublePowerRail == 1 &&
                    currentRow % static_cast<int>(
                                     (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  currentRow--;
                  continue;
                }
                FlagforSecond = 0;
                neighborCoord =
                    SMTCell::getVertex((*neighborCoord))->getBackADJ();

                if (neighborCoord->ifValid() == false) {
                  break;
                }
              }

              if (SMTCell::ifVertex((*neighborCoord)) == false) {
                break;
              }

              Triplet *neighborUpCoord;
              if (neighborCoord->ifValid()) {
                neighborUpCoord =
                    SMTCell::getVertex((*neighborCoord))->getUpADJ();
                if (!neighborUpCoord->ifValid()) {
                  std::cerr << "\nERROR : There is some bug in switch box "
                               "definition !\n";
                  std::cerr << vCoord->getVname() << "\n";
                  exit(1);
                }
              }
              if (metal > 1 && metal % 2 == 1 &&
                  SMTCell::getVertex((*neighborCoord))->getCol() % (2 * step) ==
                      step) {
                continue;
              } else {
                std::string tmp_str =
                    fmt::format("M_{}_{}", neighborCoord->getVname(),
                                SMTCell::getVertex((*neighborCoord))
                                    ->getUpADJ()
                                    ->getVname());
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
              std::cerr << "\n[ERROR] VIA2VIA: more than one G Variables "
                           "are true!!!\n";
              exit(1);
            } else {
              for (int i = 0; i < tmp_var.size(); i++) {
                SMTCell::assignTrueVar(tmp_var[i], 0, true);
              }
            }
          } else {
            if (cnt_var > 2) {
              SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
              SMTCell::writeConstraint(fmt::format(" {} (or", tmp_var[0]));
              for (auto s : tmp_var) {
                if (s == tmp_var[0]) {
                  continue;
                }
                SMTCell::writeConstraint(fmt::format(" {}", s));
                SMTCell::cnt("l", 3);
              }
              SMTCell::writeConstraint(fmt::format(")))\n"));
              SMTCell::cnt("c", 3);
            } else if (cnt_var > 1) {
              SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
              for (auto s : tmp_var) {
                SMTCell::writeConstraint(fmt::format(" {}", s));
                SMTCell::cnt("l", 3);
              }
              SMTCell::writeConstraint(fmt::format("))\n"));
              SMTCell::cnt("c", 3);
            }
          }
        }
      }
    }
  }
}

void DesignRuleWriter::write_VR_M2_M4_helper(float VR_Parameter,
                                             int doublePowerRail) {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int metal = 2; metal <= SMTCell::getNumMetalLayer() - 1; metal++) {
      int step = 0;
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && col % 2 == 1) {
          //   continue;
          // }
          if ((row == SMTCell::getNumTrackH() - 3) &&
              (col == SMTCell::getRealNumTrackV() - 1)) {
            continue;
          }
          // Via-to-via Spacing Rule
          Triplet *vCoord = new Triplet(metal, row, col);

          // check if the vertex is valid
          if (!SMTCell::ifVertex((*vCoord))) {
            continue;
          }

          if (SMTCell::getVertex((*vCoord))->getUpADJ()->ifValid()) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format(
                "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                vCoord->getVname(),
                SMTCell::getVertex((*vCoord))->getUpADJ()->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int newRow = row; newRow <= SMTCell::getNumTrackH() - 3;
                 newRow++) {
              for (int newCol = col; newCol <= SMTCell::getRealNumTrackV() - 1;
                   newCol += step) {
                int distCol = (newCol - col) / SMTCell::getMetalOneStep();
                int distRow = newRow - row;
                // Check power rail between newRow and row. (Double Power Rail
                // Rule Applying)
                if (doublePowerRail == 1 &&
                    floor(newRow / (SMTCell::getTrackEachRow() + 1)) !=
                        floor(row / (SMTCell::getTrackEachRow() + 1))) {
                  distRow++;
                }

                if (newRow == row && newCol == col) { // Initial Value
                  continue;
                }

                if ((distCol * distCol + distRow * distRow) >
                    (VR_Parameter * VR_Parameter)) { // Check the Via Distance
                  break;
                }

                // Need to consider the Power rail distance by 2 like EOL rule
                Triplet *neighborCoord = new Triplet();
                std::memcpy(neighborCoord, vCoord, sizeof(Triplet));
                //
                while (distCol > 0) {
                  distCol--;
                  neighborCoord =
                      SMTCell::getVertex((*neighborCoord))->getRightADJ();

                  if (neighborCoord->ifValid() == false) {
                    break;
                  }
                }

                int currentRow = row;
                int FlagforSecond = 0;
                //
                while (distRow > 0) {
                  distRow--;
                  currentRow++;
                  // Double Power Rail Effective Flag Code
                  if (doublePowerRail == 1 &&
                      currentRow % static_cast<int>(
                                       (SMTCell::getTrackEachRow() + 1)) ==
                          0 &&
                      FlagforSecond == 0) {
                    FlagforSecond = 1;
                    currentRow--;
                    continue;
                  }
                  FlagforSecond = 0;
                  neighborCoord =
                      SMTCell::getVertex((*neighborCoord))->getBackADJ();
                  if (neighborCoord->ifValid() == false) {
                    break;
                  }
                }

                if (SMTCell::ifVertex((*neighborCoord)) == false) {
                  break;
                }

                Triplet *neighborUpCoord;
                if (neighborCoord->ifValid()) {
                  neighborUpCoord =
                      SMTCell::getVertex((*neighborCoord))->getUpADJ();
                  if (!neighborUpCoord->ifValid()) {
                    std::cerr << "\nERROR : There is some bug in switch box "
                                 "definition !\n";
                    std::cerr << vCoord->getVname() << "\n";
                    exit(1);
                  }
                }
                if (metal > 1 && metal % 2 == 1 &&
                    SMTCell::getVertex((*neighborCoord))->getCol() %
                            (2 * step) ==
                        step) {
                  continue;
                } else {
                  std::string tmp_str = fmt::format(
                      "C_VIA_WO_N{}_E_{}_{}",
                      SMTCell::getNet(netIndex)->getNetID(),
                      neighborCoord->getVname(), neighborUpCoord->getVname());
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
                std::cerr << "\n[ERROR] VIA2VIA: more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 2) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                SMTCell::writeConstraint(fmt::format(" {} (or", tmp_var[0]));
                for (auto s : tmp_var) {
                  if (s == tmp_var[0]) {
                    continue;
                  }
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format(")))\n"));
                SMTCell::cnt("c", 3);
              } else if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }

  for (int metal = 2; metal <= SMTCell::getNumMetalLayer() - 1; metal++) {
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        // if (metal > 1 && col % 2 == 1) {
        //   continue;
        // }
        if ((row == SMTCell::getNumTrackH() - 3) &&
            (col == SMTCell::getRealNumTrackV() - 1)) {
          continue;
        }
        // Via-to-via Spacing Rule
        Triplet *vCoord = new Triplet(metal, row, col);

        // check if the vertex is valid
        if (!SMTCell::ifVertex((*vCoord))) {
          continue;
        }

        if (SMTCell::getVertex((*vCoord))->getUpADJ()->ifValid()) {
          for (int newRow = row; newRow <= SMTCell::getNumTrackH() - 3;
               newRow++) {
            for (int newCol = col; newCol <= SMTCell::getRealNumTrackV() - 1;
                 newCol += step) {
              int distCol = (newCol - col) / SMTCell::getMetalOneStep();
              int distRow = newRow - row;
              // Check power rail between newRow and row. (Double Power Rail
              // Rule Applying)
              if (doublePowerRail == 1 &&
                  floor(newRow / (SMTCell::getTrackEachRow() + 1)) !=
                      floor(row / (SMTCell::getTrackEachRow() + 1))) {
                distRow++;
              }

              if (newRow == row && newCol == col) { // Initial Value
                continue;
              }

              if ((distCol * distCol + distRow * distRow) >
                  (VR_Parameter * VR_Parameter)) { // Check the Via Distance
                break;
              }
              // Need to consider the Power rail distance by 2 like EOL rule
              Triplet *neighborCoord = new Triplet();
              std::memcpy(neighborCoord, vCoord, sizeof(Triplet));

              while (distCol > 0) {
                distCol--;
                neighborCoord =
                    SMTCell::getVertex((*neighborCoord))->getRightADJ();

                if (neighborCoord->ifValid() == false) {
                  break;
                }
              }

              if (SMTCell::ifVertex((*neighborCoord)) == false) {
                break;
              }

              int currentRow = row;
              int FlagforSecond = 0;
              while (distRow > 0) {
                distRow--;
                currentRow++;
                // Double Power Rail Effective Flag Code
                if (doublePowerRail == 1 &&
                    currentRow % static_cast<int>(
                                     (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  currentRow--;
                  continue;
                }
                FlagforSecond = 0;
                neighborCoord =
                    SMTCell::getVertex((*neighborCoord))->getBackADJ();

                if (neighborCoord->ifValid() == false) {
                  break;
                }
              }

              if (SMTCell::ifVertex((*neighborCoord)) == false) {
                break;
              }

              Triplet *neighborUpCoord;
              if (neighborCoord->ifValid()) {
                neighborUpCoord =
                    SMTCell::getVertex((*neighborCoord))->getUpADJ();
                if (!neighborUpCoord->ifValid()) {
                  std::cerr << "\nERROR : There is some bug in switch box "
                               "definition !\n";
                  std::cerr << vCoord->getVname() << "\n";
                  exit(1);
                }
              }
              if (metal > 1 && metal % 2 == 1 &&
                  SMTCell::getVertex((*neighborCoord))->getCol() % (2 * step) ==
                      step) {
                continue;
              } else {
                for (int netIndex = 0; netIndex < SMTCell::getNetCnt();
                     netIndex++) {
                  std::vector<std::string> tmp_var;
                  int cnt_var = 0;
                  int cnt_true = 0;
                  std::string tmp_str_c =
                      fmt::format("C_VIA_WO_N{}_E_{}_{}",
                                  SMTCell::getNet(netIndex)->getNetID(),
                                  neighborCoord->getVname(),
                                  SMTCell::getVertex((*neighborCoord))
                                      ->getUpADJ()
                                      ->getVname());
                  if (!SMTCell::ifAssigned(tmp_str_c)) { // DSY check:
                    // "h_var" ifAssigned
                    for (int netIndex_sub = 0;
                         netIndex_sub < SMTCell::getNetCnt(); netIndex_sub++) {
                      if (netIndex_sub == netIndex) {
                        continue;
                      }
                      std::string tmp_str =
                          fmt::format("N{}_E_{}_{}",
                                      SMTCell::getNet(netIndex_sub)->getNetID(),
                                      neighborCoord->getVname(),
                                      SMTCell::getVertex((*neighborCoord))
                                          ->getUpADJ()
                                          ->getVname());
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

                  if (cnt_true > 0) {
                    if (cnt_true > 1) {
                      std::cerr
                          << "\n[ERROR] VIA2VIA: more than one G Variables "
                             "are true!!!\n";
                      exit(1);
                    } else {
                      for (int i = 0; i < tmp_var.size(); i++) {
                        SMTCell::assignTrueVar(tmp_var[i], 0, true);
                      }
                    }
                  } else {
                    if (cnt_var > 1) {
                      SMTCell::writeConstraint(
                          fmt::format("(assert (= {} (or", tmp_str_c));
                      for (auto s : tmp_var) {
                        SMTCell::writeConstraint(fmt::format(" {}", s));
                        SMTCell::cnt("l", 3);
                      }
                      SMTCell::writeConstraint(fmt::format(")))\n"));
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

void DesignRuleWriter::write_pin_access_rule(int MPL_Parameter,
                                             int MAR_Parameter,
                                             int EOL_Parameter) {
  DesignRuleWriter::write_pin_access_rule_helper(MPL_Parameter, MAR_Parameter,
                                                 EOL_Parameter);
  // line 10029
  // ### Pin Accessibility Rule : any vias to the metal3 layer should be
  // connected to metal3 in-layer
  // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
  // [Arr. of adjacent vertices]
  // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
  // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
  SMTCell::writeConstraint(";12-A. VIA enclosure for each normal vertex\n");
  DesignRuleWriter::write_pin_access_rule_via_enclosure_helper();
  SMTCell::writeConstraint("\n");
  SMTCell::writeConstraint(
      ";[DISABLED] 12-B. VIA enclosure for each normal vertex\n");

  SMTCell::writeConstraint(";12-C. VIA23 for each vertex\n");
  DesignRuleWriter::write_pin_access_rule_via23_helper();
  SMTCell::writeConstraint("\n");
  DesignRuleWriter::write_pin_access_rule_via34_helper();
  SMTCell::writeConstraint("\n");

  // line 10295
  fmt::print("have been written.\n");
}

void DesignRuleWriter::write_pin_access_rule_helper(int MPL_Parameter,
                                                    int MAR_Parameter,
                                                    int EOL_Parameter) {
  int metal = SMTCell::getNumMetalLayer() - 1;
  int step = 0;
  if (metal == 1) {
    step = SMTCell::getMetalOneStep();
  } else if (metal >= 3) {
    step = SMTCell::getMetalThreeStep();
  } else {
    // # Metal 2 (M0)
    step = SMTCell::getGCDStep();
  }
  std::map<std::string, int> h_tmp;

  // #Vertical
  for (auto en : SMTCell::getExtNet()) {
    int netIndex_i = SMTCell::getNetIdx(std::to_string(en.first));
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

          if (SMTCell::ifVertex((*vCoord_i)) == false) {
            continue;
          }

          if (SMTCell::ifVEdgeOut(vCoord_i->getVname())) {
            for (int i : SMTCell::getVEdgeOut(vCoord_i->getVname())) {
              for (int commodityIndex = 0;
                   commodityIndex < SMTCell::getNet(netIndex_i)->getNumSinks();
                   commodityIndex++) {
                if (SMTCell::getVirtualEdge(i)->getPinName() ==
                        SMTCell::getNet(netIndex_i)
                            ->getSinks_inNet(commodityIndex) &&
                    SMTCell::getVirtualEdge(i)->getPinName() == Pin::keySON) {
                  if (h_tmp.find(tmp_net_col_name) == h_tmp.end()) {
                    h_tmp[tmp_net_col_name] = 1;
                  }

                  std::string tmp_str_i = fmt::format(
                      "N{}_E_{}_{}", SMTCell::getNet(netIndex_i)->getNetID(),
                      vCoord_i->getVname(),
                      SMTCell::getVirtualEdge(i)->getPinName());

                  // check declaration
                  if (!SMTCell::ifAssigned(tmp_str_i)) {
                    SMTCell::setVar(tmp_str_i, 2);
                    SMTCell::writeConstraint(fmt::format(
                        "(assert (ite (and (= N{}_M2_TRACK false) (= "
                        "{} true)) ((_ at-least {})",
                        en.first, tmp_str_i, MPL_Parameter));
                  } else if (SMTCell::ifAssignedTrue(tmp_str_i)) {
                    SMTCell::setVar_wo_cnt(tmp_str_i, 0);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= N{}_M2_TRACK false) ((_ "
                                    "at-least {})",
                                    en.first, MPL_Parameter));
                  }

                  for (int row_j = 0; row_j <= SMTCell::getNumTrackH() - 3;
                       row_j++) {
                    std::string tmp_str_j = "";

                    std::vector<std::string> tmp_var_i;
                    int cnt_var_i = 0;
                    int cnt_true_i = 0;

                    std::vector<std::string> tmp_var_j;
                    int cnt_var_j = 0;
                    int cnt_true_j = 0;

                    Triplet *vCoord_j = new Triplet(metal, row_j, col);
                    if (SMTCell::ifVertex((*vCoord_j)) &&
                        SMTCell::getVertex((*vCoord_j))
                            ->getFrontADJ()
                            ->ifValid()) {
                      std::string curr_front_variable =
                          fmt::format("N{}_E_{}_{}", en.first,
                                      SMTCell::getVertex((*vCoord_j))
                                          ->getFrontADJ()
                                          ->getVname(),
                                      vCoord_j->getVname());
                      // check declaration
                      if (!SMTCell::ifAssigned(curr_front_variable)) {
                        tmp_var_j.push_back(curr_front_variable);
                        SMTCell::setVar(curr_front_variable, 2);
                        cnt_var_j++;
                      } else if (SMTCell::ifAssignedTrue(curr_front_variable)) {
                        SMTCell::setVar_wo_cnt(curr_front_variable, 2);
                        cnt_true_j++;
                      }
                    }

                    if (SMTCell::ifVertex((*vCoord_j)) &&
                        SMTCell::getVertex((*vCoord_j))
                            ->getBackADJ()
                            ->ifValid()) {
                      std::string curr_back_variable = fmt::format(
                          "N{}_E_{}_{}", en.first, vCoord_j->getVname(),
                          SMTCell::getVertex((*vCoord_j))
                              ->getBackADJ()
                              ->getVname());
                      // check declaration
                      if (!SMTCell::ifAssigned(curr_back_variable)) {
                        tmp_var_j.push_back(curr_back_variable);
                        SMTCell::setVar(curr_back_variable, 2);
                        cnt_var_j++;
                      } else if (SMTCell::ifAssignedTrue(curr_back_variable)) {
                        SMTCell::setVar_wo_cnt(curr_back_variable, 2);
                        cnt_true_j++;
                      }
                    }

                    SMTCell::writeConstraint(" (or");

                    for (int mar = 0; mar <= MAR_Parameter; mar++) {
                      // potentila bug? why redeclaration
                      tmp_var_i.clear();
                      cnt_var_i = 0;
                      cnt_true_i = 0;

                      // # Upper Layer => Left = EOL, Right = EOL+MAR should
                      // be keepout region from other nets
                      Triplet *vCoord_j = new Triplet(metal + 1, row_j, col);

                      if (SMTCell::ifVertex((*vCoord_j)) == false) {
                        continue;
                      }
                      // fmt::print("vCoord_j:{}\n", vCoord_j->getVname());
                      for (int netIndex_j = 0;
                           netIndex_j < SMTCell::getNetCnt(); netIndex_j++) {
                        if (SMTCell::getNet(netIndex_j)->getNetID() !=
                            std::to_string(en.first)) {
                          // Deep copy mem
                          Triplet *prev_left_vCoord = new Triplet();
                          std::memcpy(prev_left_vCoord, vCoord_j,
                                      sizeof(Triplet));
                          // fmt::print("prev_left_vCoord:{}\n",
                          //  prev_left_vCoord->getVname());
                          for (int i = 0; i <= (EOL_Parameter + mar); i++) {
                            if (SMTCell::ifVertex((*prev_left_vCoord)) &&
                                SMTCell::getVertex((*prev_left_vCoord))
                                    ->getLeftADJ()
                                    ->ifValid()) {
                              tmp_str_j = fmt::format(
                                  "N{}_E_{}_{}",
                                  SMTCell::getNet(netIndex_j)->getNetID(),
                                  SMTCell::getVertex((*prev_left_vCoord))
                                      ->getLeftADJ()
                                      ->getVname(),
                                  prev_left_vCoord->getVname());
                              // fmt::print("tmp_str_j1 {}\n", tmp_str_j);
                              // check declaration
                              if (!SMTCell::ifAssigned(tmp_str_j)) {
                                tmp_var_i.push_back(tmp_str_j);
                                SMTCell::setVar(tmp_str_j, 2);
                                cnt_var_i++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str_j)) {
                                SMTCell::setVar_wo_cnt(tmp_str_j, 2);
                                cnt_true_i++;
                              }
                              prev_left_vCoord =
                                  SMTCell::getVertex((*prev_left_vCoord))
                                      ->getLeftADJ();
                            } else {
                              continue;
                            }
                          }

                          Triplet *prev_right_vCoord = new Triplet();
                          std::memcpy(prev_right_vCoord, vCoord_j,
                                      sizeof(Triplet));
                          // bug found on ifValid()
                          // fmt::print("prev_right_vCoord:{} {} {}\n",
                          // prev_right_vCoord->getVname(),
                          // SMTCell::ifVertex((*prev_right_vCoord)),
                          // SMTCell::getVertex((*prev_right_vCoord))
                          //           ->getLeftADJ()
                          //           ->ifValid());
                          for (int i = 0;
                               i <= (MAR_Parameter - mar + EOL_Parameter);
                               i++) {
                            if (SMTCell::ifVertex((*prev_right_vCoord)) &&
                                SMTCell::getVertex((*prev_right_vCoord))
                                    ->getRightADJ()
                                    ->ifValid()) {
                              tmp_str_j = fmt::format(
                                  "N{}_E_{}_{}",
                                  SMTCell::getNet(netIndex_j)->getNetID(),
                                  prev_right_vCoord->getVname(),
                                  SMTCell::getVertex((*prev_right_vCoord))
                                      ->getRightADJ()
                                      ->getVname());
                              // fmt::print("tmp_str_j2 {}\n", tmp_str_j);
                              // check declaration
                              if (!SMTCell::ifAssigned(tmp_str_j)) {
                                tmp_var_i.push_back(tmp_str_j);
                                SMTCell::setVar(tmp_str_j, 2);
                                cnt_var_i++;
                              } else if (SMTCell::ifAssignedTrue(tmp_str_j)) {
                                SMTCell::setVar_wo_cnt(tmp_str_j, 2);
                                cnt_true_i++;
                              }
                              prev_right_vCoord =
                                  SMTCell::getVertex((*prev_right_vCoord))
                                      ->getRightADJ();
                            } else {
                              continue;
                            }
                          }
                        }
                      }
                      // fmt::print("cnt_true_i {}\n", cnt_true_i);
                      // fmt::print("cnt_true_j {}\n", cnt_true_j);
                      // fmt::print("cnt_var_i {}\n", cnt_var_i);
                      // fmt::print("cnt_var_j {}\n", cnt_var_j);
                      if (cnt_true_j > 0) {
                        if (cnt_true_i == 0) {
                          if (cnt_var_i == 1) {
                            SMTCell::writeConstraint(
                                fmt::format(" (= {} false)", tmp_var_i[0]));
                            SMTCell::cnt("l", 3);
                          } else if (cnt_var_i > 1) {
                            SMTCell::writeConstraint(" (and");
                            for (int m = 0; m < tmp_var_i.size(); m++) {
                              SMTCell::writeConstraint(
                                  fmt::format(" (= {} false)", tmp_var_i[m]));
                              SMTCell::cnt("l", 3);
                            }
                            SMTCell::writeConstraint(")");
                          }
                        }
                      } else if (cnt_var_j > 0) {
                        if (cnt_true_i == 0) {
                          if (cnt_var_j == 1) {
                            SMTCell::writeConstraint(
                                fmt::format(" (and (= {} true)", tmp_var_j[0]));
                            SMTCell::cnt("l", 3);
                            for (int m = 0; m < tmp_var_i.size(); m++) {
                              SMTCell::writeConstraint(
                                  fmt::format(" (= {} false)", tmp_var_i[m]));
                              SMTCell::cnt("l", 3);
                            }
                            SMTCell::writeConstraint(")");
                          } else {
                            SMTCell::writeConstraint(
                                fmt::format(" (and (or", tmp_var_j[0]));
                            for (int m = 0; m < tmp_var_j.size(); m++) {
                              SMTCell::writeConstraint(
                                  fmt::format(" (= {} true)", tmp_var_j[m]));
                              SMTCell::cnt("l", 3);
                            }
                            SMTCell::writeConstraint(")");
                            for (int m = 0; m < tmp_var_i.size(); m++) {
                              SMTCell::writeConstraint(
                                  fmt::format(" (= {} false)", tmp_var_i[m]));
                              SMTCell::cnt("l", 3);
                            }
                            SMTCell::writeConstraint(")");
                          }
                        }
                      }
                    }
                    SMTCell::writeConstraint(")");
                  }
                  if (!SMTCell::ifAssigned(tmp_str_i) ||
                      SMTCell::ifAssignedTrue(tmp_str_i)) {
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
  // fmt::print("have been written.\n");
}

void DesignRuleWriter::write_pin_access_rule_via_enclosure_helper() {
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int metal = 1; metal <= SMTCell::getNumMetalLayer() - 1; metal++) {
      int step = 0;
      if (metal == 1) {
        step = SMTCell::getMetalOneStep();
      } else if (metal >= 3) {
        step = SMTCell::getMetalThreeStep();
      } else {
        // # Metal 2 (M0)
        step = SMTCell::getGCDStep();
      }
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          Triplet *vCoord_Up = SMTCell::getVertex((*vCoord))->getUpADJ();

          if (SMTCell::ifVertex((*vCoord_Up)) == false) {
            continue;
          }

          std::string tmp_i = fmt::format(
              "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              vCoord->getVname(),
              SMTCell::getVertex((*vCoord))->getUpADJ()->getVname());
          std::string tmp_j = "";
          std::string tmp_k = "";

          // horizontal direction
          if (metal % 2 == 0) {
            // Front Vertex
            // potential bug, this should be vCoord_Up?
            // fmt::print("vCoord_Up Name: {}\n", vCoord_Up->getVname());
            if (SMTCell::getVertex((*vCoord_Up))->getFrontADJ()->ifValid()) {
              tmp_j = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  SMTCell::getVertex((*vCoord_Up))->getFrontADJ()->getVname(),
                  vCoord_Up->getVname());
            } else {
              tmp_j = "null";
            }

            // Back Vertex
            if (SMTCell::getVertex((*vCoord_Up))->getBackADJ()->ifValid()) {
              tmp_k = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  vCoord_Up->getVname(),
                  SMTCell::getVertex((*vCoord_Up))->getBackADJ()->getVname());
            } else {
              tmp_k = "null";
            }
          } else {
            // vertical direction
            // Left Vertex
            if (SMTCell::getVertex((*vCoord_Up))->getLeftADJ()->ifValid()) {
              tmp_j = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  SMTCell::getVertex((*vCoord_Up))->getLeftADJ()->getVname(),
                  vCoord_Up->getVname());
            } else {
              tmp_j = "null";
            }

            // Right Vertex
            if (SMTCell::getVertex((*vCoord_Up))->getRightADJ()->ifValid()) {
              tmp_k = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  vCoord_Up->getVname(),
                  SMTCell::getVertex((*vCoord_Up))->getRightADJ()->getVname());
            } else {
              tmp_k = "null";
            }
          }

          if (tmp_j == "null" || SMTCell::ifAssignedFalse(tmp_j)) {
            if (tmp_k == "null" || SMTCell::ifAssignedFalse(tmp_k)) {
              fmt::print("FLAG10: write_pin_access_rule\n");
              SMTCell::setVar(tmp_i, 6);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (= {} true) (= true false) (= true true)))\n",
                  tmp_i));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            } else if (tmp_k != "null" && !SMTCell::ifAssigned(tmp_k)) {
              SMTCell::setVar(tmp_i, 6);
              SMTCell::setVar(tmp_k, 6);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (= {} true) (= {} true) (= true true)))\n",
                  tmp_i, tmp_k));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          } else if (tmp_j != "null" && !SMTCell::ifAssigned(tmp_j)) {
            if (tmp_k == "null" || SMTCell::ifAssignedFalse(tmp_k)) {
              SMTCell::setVar(tmp_i, 6);
              SMTCell::setVar(tmp_j, 6);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (= {} true) (= {} true) (= true true)))\n",
                  tmp_i, tmp_j));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            } else if (tmp_k != "null" && !SMTCell::ifAssigned(tmp_k)) {
              SMTCell::setVar(tmp_i, 6);
              SMTCell::setVar(tmp_j, 6);
              SMTCell::setVar(tmp_k, 6);
              SMTCell::writeConstraint(
                  fmt::format("(assert (ite (= {} true) ((_ at-least 1) {} "
                              "{}) (= true true)))\n",
                              tmp_i, tmp_j, tmp_k));
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("l", 3);
              SMTCell::cnt("c", 3);
            }
          }
        }
      }
    }
  }
}

void DesignRuleWriter::write_pin_access_rule_via23_helper() {
  for (auto en : SMTCell::getExtNet()) {
    int netIndex = SMTCell::getNetIdx(std::to_string(en.first));
    // only subject to M3 (M1)
    int metal = 3;
    int step = SMTCell::getMetalThreeStep();
    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
        if (col % SMTCell::getMetalOneStep() != 0 &&
            col % SMTCell::getMetalThreeStep() != 0) {
          continue;
        }
        // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
        //   continue;
        // }
        Triplet *vCoord = new Triplet(metal, row, col);

        if (SMTCell::ifVertex((*vCoord)) == false) {
          continue;
        }

        if (SMTCell::ifVEdgeOut(vCoord->getVname())) {
          for (int i : SMTCell::getVEdgeOut(vCoord->getVname())) {
            std::string vName_i = SMTCell::getVirtualEdge(i)->getVName();
            std::string vName_j = SMTCell::getVirtualEdge(i)->getPinName();

            std::string tmp_i =
                fmt::format("N{}_E_{}_{}", en.first, vName_i, vName_j);
            std::string tmp_j = fmt::format(
                "N{}_E_{}_{}", en.first,
                SMTCell::getVertex((*vCoord))->getDownADJ()->getVname(),
                vCoord->getVname());

            // Front Vertex
            std::string tmp_k;
            if (SMTCell::getVertex((*vCoord))->getFrontADJ()->ifValid()) {
              tmp_k = fmt::format(
                  "N{}_E_{}_{}", en.first,
                  SMTCell::getVertex((*vCoord))->getFrontADJ()->getVname(),
                  vCoord->getVname());
            } else {
              tmp_k = fmt::format("N{}_E_{}_{}", en.first, vCoord->getVname(),
                                  "FrontEnd");
            }

            // Back Vertex
            std::string tmp_h;
            if (SMTCell::getVertex((*vCoord))->getBackADJ()->ifValid()) {
              tmp_h = fmt::format(
                  "N{}_E_{}_{}", en.first, vCoord->getVname(),
                  SMTCell::getVertex((*vCoord))->getBackADJ()->getVname());
            } else {
              tmp_h = fmt::format("N{}_E_{}_{}", en.first, vCoord->getVname(),
                                  "BackEnd");
            }

            if (!SMTCell::ifAssigned(tmp_i) && !SMTCell::ifAssigned(tmp_j)) {
              if (SMTCell::ifAssignedFalse(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (and (= {} true) (= {} "
                                  "true)) (= true false) (= true true)))\n",
                                  tmp_i, tmp_j));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_k)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (and (= {} true) (= {} "
                                  "true)) (= {} true) (= true true)))\n",
                                  tmp_i, tmp_j, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                }
              } else if (!SMTCell::ifAssigned(tmp_h)) {
                if (SMTCell::ifAssignedFalse(tmp_k)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (and (= {} true) (= {} "
                                  "true)) (= {} true) (= true true)))\n",
                                  tmp_i, tmp_j, tmp_k));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_k)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::setVar(tmp_h, 6);
                  SMTCell::writeConstraint(fmt::format(
                      "(assert (ite (and (= {} true) (= {} true)) ((_ "
                      "at-least 1) {} {}) (= true true)))\n",
                      tmp_i, tmp_j, tmp_k, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                }
              }
            } else if (SMTCell::ifAssignedTrue(tmp_i) &&
                       SMTCell::ifAssignedTrue(tmp_j)) {
              if (SMTCell::ifAssignedFalse(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  fmt::print("[ERROR] MPL : UNSAT Condition!!!\n");
                  exit(-1);
                }
              }
            } else if (SMTCell::ifAssignedTrue(tmp_i)) {
              if (SMTCell::ifAssignedFalse(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= true false) "
                                  "(= true true)))\n",
                                  tmp_j));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_h)) {
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_h, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= {} true) "
                                  "(= true true)))\n",
                                  tmp_j, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                }
              } else if (!SMTCell::ifAssigned(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= {} true) "
                                  "(= true true)))\n",
                                  tmp_j, tmp_k));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_h)) {
                  SMTCell::setVar(tmp_j, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::setVar(tmp_h, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) ((_ at-least 1) "
                                  "{} {}) (= true true)))\n",
                                  tmp_j, tmp_k, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                }
              }
            } else if (SMTCell::ifAssignedTrue(tmp_j)) {
              if (SMTCell::ifAssignedFalse(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= true false) "
                                  "(= true true)))\n",
                                  tmp_i));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_h)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_h, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= {} true) "
                                  "(= true true)))\n",
                                  tmp_i, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                }
              } else if (!SMTCell::ifAssigned(tmp_k)) {
                if (SMTCell::ifAssignedFalse(tmp_h)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) (= {} true) "
                                  "(= true true)))\n",
                                  tmp_i, tmp_k));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("c", 3);
                } else if (!SMTCell::ifAssigned(tmp_h)) {
                  SMTCell::setVar(tmp_i, 6);
                  SMTCell::setVar(tmp_k, 6);
                  SMTCell::setVar(tmp_h, 6);
                  SMTCell::writeConstraint(
                      fmt::format("(assert (ite (= {} true) ((_ at-least 1) "
                                  "{} {}) (= true true)))\n",
                                  tmp_i, tmp_k, tmp_h));
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
                  SMTCell::cnt("l", 3);
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

void DesignRuleWriter::write_pin_access_rule_via34_helper() {
  if (SMTCell::getNumMetalLayer() >= 4) {
    SMTCell::writeConstraint(";12-D. VIA34 for each vertex\n");
    // Mergable with above
    for (auto en : SMTCell::getExtNet()) {
      int netIndex = SMTCell::getNetIdx(std::to_string(en.first));
      // only subject to M3 (M1)
      int metal = 3;
      int step = SMTCell::getMetalThreeStep();
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          if (SMTCell::ifVEdgeOut(vCoord->getVname())) {
            for (int i : SMTCell::getVEdgeOut(vCoord->getVname())) {
              std::string vName_i = SMTCell::getVirtualEdge(i)->getVName();
              std::string vName_j = SMTCell::getVirtualEdge(i)->getPinName();

              std::string tmp_i =
                  fmt::format("N{}_E_{}_{}", en.first, vName_i, vName_j);
              // mergable flag: change up to down
              std::string tmp_j = fmt::format(
                  "N{}_E_{}_{}", en.first, vCoord->getVname(),
                  SMTCell::getVertex((*vCoord))->getUpADJ()->getVname());

              // Front Vertex
              std::string tmp_k;
              if (SMTCell::getVertex((*vCoord))->getFrontADJ()->ifValid()) {
                tmp_k = fmt::format(
                    "N{}_E_{}_{}", en.first,

                    SMTCell::getVertex((*vCoord))->getFrontADJ()->getVname(),
                    vCoord->getVname());
              } else {
                tmp_k = fmt::format("N{}_E_{}_{}", en.first, vCoord->getVname(),
                                    "FrontEnd");
              }

              // Back Vertex
              std::string tmp_h;
              if (SMTCell::getVertex((*vCoord))->getBackADJ()->ifValid()) {
                tmp_h = fmt::format(
                    "N{}_E_{}_{}", en.first, vCoord->getVname(),
                    SMTCell::getVertex((*vCoord))->getBackADJ()->getVname());
              } else {
                tmp_h = fmt::format("N{}_E_{}_{}", en.first, vCoord->getVname(),
                                    "BackEnd");
              }

              if (!SMTCell::ifAssigned(tmp_i) && !SMTCell::ifAssigned(tmp_j)) {
                if (SMTCell::ifAssignedFalse(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (and (= {} true) (= {} "
                                    "true)) (= true false) (= true true)))\n",
                                    tmp_i, tmp_j));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_k)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (and (= {} true) (= {} "
                                    "true)) (= {} true) (= true true)))\n",
                                    tmp_i, tmp_j, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                } else if (!SMTCell::ifAssigned(tmp_h)) {
                  if (SMTCell::ifAssignedFalse(tmp_k)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (and (= {} true) (= {} "
                                    "true)) (= {} true) (= true true)))\n",
                                    tmp_i, tmp_j, tmp_k));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_k)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::setVar(tmp_h, 6);
                    SMTCell::writeConstraint(fmt::format(
                        "(assert (ite (and (= {} true) (= {} true)) ((_ "
                        "at-least 1) {} {}) (= true true)))\n",
                        tmp_i, tmp_j, tmp_k, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                }
              } else if (SMTCell::ifAssignedTrue(tmp_i) &&
                         SMTCell::ifAssignedTrue(tmp_j)) {
                if (SMTCell::ifAssignedFalse(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    fmt::print("[ERROR] MPL : UNSAT Condition!!!\n");
                    exit(-1);
                  }
                }
              } else if (SMTCell::ifAssignedTrue(tmp_i)) {
                if (SMTCell::ifAssignedFalse(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= true false) "
                                    "(= true true)))\n",
                                    tmp_j));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_h)) {
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_h, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= {} true) "
                                    "(= true true)))\n",
                                    tmp_j, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                } else if (!SMTCell::ifAssigned(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= {} true) "
                                    "(= true true)))\n",
                                    tmp_j, tmp_k));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_h)) {
                    SMTCell::setVar(tmp_j, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::setVar(tmp_h, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) ((_ at-least 1) "
                                    "{} {}) (= true true)))\n",
                                    tmp_j, tmp_k, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                }
              } else if (SMTCell::ifAssignedTrue(tmp_j)) {
                if (SMTCell::ifAssignedFalse(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= true false) "
                                    "(= true true)))\n",
                                    tmp_i));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_h)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_h, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= {} true) "
                                    "(= true true)))\n",
                                    tmp_i, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                } else if (!SMTCell::ifAssigned(tmp_k)) {
                  if (SMTCell::ifAssignedFalse(tmp_h)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) (= {} true) "
                                    "(= true true)))\n",
                                    tmp_i, tmp_k));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  } else if (!SMTCell::ifAssigned(tmp_h)) {
                    SMTCell::setVar(tmp_i, 6);
                    SMTCell::setVar(tmp_k, 6);
                    SMTCell::setVar(tmp_h, 6);
                    SMTCell::writeConstraint(
                        fmt::format("(assert (ite (= {} true) ((_ at-least 1) "
                                    "{} {}) (= true true)))\n",
                                    tmp_i, tmp_k, tmp_h));
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("l", 3);
                    SMTCell::cnt("c", 3);
                  }
                }
              }
            }
          }
        }
      }
    }
    SMTCell::writeConstraint("\n");
  }
}

/**
 * Parallel Run Length (PRL) rule:
 * Enforces the avoidance of “single-pointcontact” in SADP mask manufacturing
 *
 * @note
 * Example: (PRL = 2) No Violation
 * ----X====X====X===
 *     |    |    |
 * =========X====X
 *     |    |    |
 * ----X====X====X===
 *
 * @param   PRL_Parameter   Distance in Graph
 * @param   doublePowerRail If using Double Power Rail
 *
 * @return  void
 */
void DesignRuleWriter::write_PRL_rule(int PRL_Parameter, int doublePowerRail) {
  SMTCell::writeConstraint(";10. Parallel Run Length Rule\n");
  if (PRL_Parameter == 0) {
    std::cout << "is disable....\n";
    SMTCell::writeConstraint(";PRL is disable\n");
  } else {
    // # PRL Rule Enable /Disable
    // ### Paralle Run-Length Rule to prevent from having too close metal
    // tips.
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    SMTCell::writeConstraint(
        fmt::format(";10-A. from Right Tip to Left Tips for each vertex\n"));
    DesignRuleWriter::write_PRL_RL_tip_helper(PRL_Parameter);
    SMTCell::writeConstraint("\n");

    // Skip to check exact adjacent GV variable, (From right to left is
    // enough) 10-B is executed when PRL_Parameter > 1
    SMTCell::writeConstraint(
        fmt::format(";10-B. from Left Tip to Right Tips for each vertex\n"));
    DesignRuleWriter::write_PRL_LR_tip_helper(PRL_Parameter);
    SMTCell::writeConstraint("\n");

    // DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos] [Arr. of
    // adjacent vertices] DATA STRUCTURE:  ADJACENT_VERTICES [0:Left]
    // [1:Right] [2:Front] [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL]
    // [9:BR]

    // one Power Rail vertice has 2 times cost of other vertices. ($Double
    // Power Rail)
    SMTCell::writeConstraint(
        fmt::format(";10-C. from Back Tip to Front Tips for each vertex\n"));
    DesignRuleWriter::write_PRL_BF_tip_helper(PRL_Parameter, doublePowerRail);
    SMTCell::writeConstraint("\n");

    SMTCell::writeConstraint(
        fmt::format(";10-D. from Front Tip to Back Tips for each vertex\n"));
    DesignRuleWriter::write_PRL_FB_tip_helper(PRL_Parameter, doublePowerRail);
    SMTCell::writeConstraint("\n");
    std::cout << "have been written.\n";
  }
}

/**
 * @note
 *                            ----+----X====X==== <--- B Direction Checking
 *                                |    |    |
 *                            ▒▒▒▒▒▒▒▒▒X----+----
 *                                ║    |    |
 *                            ----+----X====X==== <--- F Direction Checking
 */
void DesignRuleWriter::write_PRL_RL_tip_helper(int PRL_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) { // M2
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // F Direction Checking
          Triplet *vCoord_F = SMTCell::getVertex((*vCoord))->getFrontADJ();

          if (SMTCell::ifVertex((*vCoord_F)) == false) {
            continue;
          }

          if (vCoord_F->ifValid() && row != 0) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            for (int prlIndex = 0; prlIndex <= PRL_Parameter - 1; prlIndex++) {
              std::string tmp_str =
                  fmt::format("GL_V_{}", vCoord_F->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              if (prlIndex != (PRL_Parameter - 1)) {
                vCoord_F = SMTCell::getVertex((*vCoord_F))->getLeftADJ();
                if (vCoord_F->ifValid() == false) {
                  break;
                }
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
          // B Direction Checking
          Triplet *vCoord_B = SMTCell::getVertex((*vCoord))->getBackADJ();

          if (SMTCell::ifVertex((*vCoord_B)) == false) {
            continue;
          }

          if (vCoord_B->ifValid() && row != (SMTCell::getNumTrackH() - 3)) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GR_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            for (int prlIndex = 0; prlIndex <= PRL_Parameter - 1; prlIndex++) {
              std::string tmp_str =
                  fmt::format("GL_V_{}", vCoord_B->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              if (prlIndex != (PRL_Parameter - 1)) {
                vCoord_B = SMTCell::getVertex((*vCoord_B))->getLeftADJ();
                if (vCoord_B->ifValid() == false) {
                  break;
                }
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 *                            ====X====X----+---- <--- B Direction Checking
 *                                |    |    |
 *                            ----+----X▒▒▒▒▒▒▒▒▒
 *                                ║    |    |
 *                            ====X====X----+---- <--- F Direction Checking
 */
void DesignRuleWriter::write_PRL_LR_tip_helper(int PRL_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) { // M2
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        if (row == 0 || row == (SMTCell::getNumTrackH() - 3)) {
          // skip the PRL rule related with power Rail.
        }
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // FR Direction Checking
          Triplet *vCoord_FR =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();

          if (SMTCell::ifVertex((*vCoord_FR)) == false) {
            continue;
          }

          if (vCoord_FR->ifValid() && row != 0 && PRL_Parameter > 1) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2; prlIndex++) {
              std::string tmp_str =
                  fmt::format("GR_V_{}", vCoord_FR->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              vCoord_FR = SMTCell::getVertex((*vCoord_FR))->getRightADJ();

              if (vCoord_FR->ifValid() == false) {
                break;
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
          // BR Direction Checking
          Triplet *vCoord_BR = SMTCell::getVertex((*vCoord))->getBackRightADJ();

          if (SMTCell::ifVertex((*vCoord_BR)) == false) {
            continue;
          }

          if (vCoord_BR->ifValid() && row != (SMTCell::getNumTrackH() - 3) &&
              PRL_Parameter > 1) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GL_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2; prlIndex++) {
              std::string tmp_str =
                  fmt::format("GR_V_{}", vCoord_BR->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              vCoord_BR = SMTCell::getVertex((*vCoord_BR))->getRightADJ();
              if (vCoord_BR->ifValid() == false) {
                break;
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 *                                |    ▒    |
 *                            ----+----▒----+----
 *                                |    ▒    |
 *  L Direction Checking ---> ----X----X----X---- <--- R Direction Checking
 *                                ║    |    ║
 *                            ----X----+----X----
 *                                ║    |    ║
 */
void DesignRuleWriter::write_PRL_BF_tip_helper(int PRL_Parameter,
                                               int doublePowerRail) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    break; // DSY
    if (metal % 2 == 1) {
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // Left Track Checking
          Triplet *vCoord_L = SMTCell::getVertex((*vCoord))->getLeftADJ();

          if (SMTCell::ifVertex((*vCoord_L)) == false) {
            continue;
          }

          if (vCoord_L->ifValid()) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GB_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            tmp_str = fmt::format("GF_V_{}", vCoord_L->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            if (PRL_Parameter > 1) {
              int newRow = row - 1;
              int FlagforSecond = 0;
              for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2;
                   prlIndex++) {
                if (doublePowerRail == 1 &&
                    newRow % static_cast<int>(
                                 (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  continue;
                }
                FlagforSecond = 0;

                vCoord_L = SMTCell::getVertex((*vCoord_L))->getFrontADJ();
                if (vCoord_L->ifValid() == false) {
                  break;
                }
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord_L->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                newRow--;
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
          // Right Track Checking
          Triplet *vCoord_R = SMTCell::getVertex((*vCoord))->getRightADJ();
          if (vCoord_R->ifValid()) {
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;
            std::string tmp_str = fmt::format("GB_V_{}", vCoord->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            tmp_str = fmt::format("GF_V_{}", vCoord_R->getVname());
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssigned(tmp_str) &&
                       SMTCell::getAssigned(tmp_str) == 1) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }
            if (PRL_Parameter > 1) {
              int newRow = row - 1;
              int FlagforSecond = 0;
              for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2;
                   prlIndex++) {
                if (doublePowerRail == 1 &&
                    newRow % static_cast<int>(
                                 (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  continue;
                }
                FlagforSecond = 0;
                vCoord_R = SMTCell::getVertex((*vCoord_R))->getFrontADJ();
                if (vCoord_R->ifValid() == false) {
                  break;
                }
                std::string tmp_str =
                    fmt::format("GF_V_{}", vCoord_R->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                newRow--;
              }
            }
            if (cnt_true > 0) {
              if (cnt_true > 1) {
                std::cerr << "\n[ERROR] PRL : more than one G Variables "
                             "are true!!!\n";
                exit(1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  if (!SMTCell::ifAssigned(tmp_var[i])) {
                    SMTCell::assignTrueVar(tmp_var[i], 0, true);
                  }
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint(fmt::format("(assert ((_ at-most 1)"));
                for (auto s : tmp_var) {
                  SMTCell::writeConstraint(fmt::format(" {}", s));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint(fmt::format("))\n"));
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 *                                ║    |    ║
 *                            ----X----+----X----
 *                                ║    |    ║
 *  L Direction Checking ---> ----X----X----X---- <--- R Direction Checking
 *                                |    ▒    |
 *                            ----+----▒----+----
 *                                |    ▒    |
 */
void DesignRuleWriter::write_PRL_FB_tip_helper(int PRL_Parameter,
                                               int doublePowerRail) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    break; // DSY
    if (metal % 2 == 1) {
      for (int row = 0; row <= SMTCell::getNumTrackH() - 4; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
          //   continue;
          // }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // Left Track Checking
          Triplet *vCoord_L = SMTCell::getVertex((*vCoord))->getLeftADJ();

          if (SMTCell::ifVertex((*vCoord_L)) == false) {
            continue;
          }

          if (vCoord_L->ifValid() && PRL_Parameter > 1) {
            int newRow = row + 1;
            if (doublePowerRail == 1 &&
                newRow % static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                    0 &&
                PRL_Parameter == 2) {
              // Nothing
            } else {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GF_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              int FlagforSecond = 0;
              for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2;
                   prlIndex++) {
                if (doublePowerRail == 1 &&
                    newRow % static_cast<int>(
                                 (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  continue;
                }
                FlagforSecond = 0;
                vCoord_L = SMTCell::getVertex((*vCoord_L))->getBackADJ();
                if (vCoord_L->ifValid() == false) {
                  break;
                }
                std::string tmp_str =
                    fmt::format("GB_V_{}", vCoord_L->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                newRow++;
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] PRL : more than one G Variables "
                               "are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    if (!SMTCell::ifAssigned(tmp_var[i])) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
                  SMTCell::cnt("c", 3);
                }
              }
            }
          }
          // Right Track Checking
          Triplet *vCoord_R = SMTCell::getVertex((*vCoord))->getRightADJ();

          if (SMTCell::ifVertex((*vCoord_R)) == false) {
            continue;
          }

          if (vCoord_R->ifValid() && PRL_Parameter > 1) {
            int newRow = row + 1;
            if (doublePowerRail == 1 &&
                newRow % static_cast<int>((SMTCell::getTrackEachRow() + 1)) ==
                    0 &&
                PRL_Parameter == 2) {
              // Nothing
            } else {
              std::vector<std::string> tmp_var;
              int cnt_var = 0;
              int cnt_true = 0;
              std::string tmp_str = fmt::format("GF_V_{}", vCoord->getVname());
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssigned(tmp_str) &&
                         SMTCell::getAssigned(tmp_str) == 1) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }
              int FlagforSecond = 0;
              for (int prlIndex = 0; prlIndex <= PRL_Parameter - 2;
                   prlIndex++) {
                if (doublePowerRail == 1 &&
                    newRow % static_cast<int>(
                                 (SMTCell::getTrackEachRow() + 1)) ==
                        0 &&
                    FlagforSecond == 0) {
                  FlagforSecond = 1;
                  continue;
                }
                FlagforSecond = 0;
                vCoord_R = SMTCell::getVertex((*vCoord_R))->getBackADJ();
                if (vCoord_R->ifValid() == false) {
                  break;
                }
                std::string tmp_str =
                    fmt::format("GB_V_{}", vCoord_R->getVname());
                if (!SMTCell::ifAssigned(tmp_str)) {
                  tmp_var.push_back(tmp_str);
                  SMTCell::setVar(tmp_str, 2);
                  cnt_var++;
                } else if (SMTCell::ifAssigned(tmp_str) &&
                           SMTCell::getAssigned(tmp_str) == 1) {
                  SMTCell::setVar_wo_cnt(tmp_str, 0);
                  cnt_true++;
                }
                newRow++;
              }
              if (cnt_true > 0) {
                if (cnt_true > 1) {
                  std::cerr << "\n[ERROR] PRL : more than one G Variables "
                               "are true!!!\n";
                  exit(1);
                } else {
                  for (int i = 0; i < tmp_var.size(); i++) {
                    if (!SMTCell::ifAssigned(tmp_var[i])) {
                      SMTCell::assignTrueVar(tmp_var[i], 0, true);
                    }
                  }
                }
              } else {
                if (cnt_var > 1) {
                  SMTCell::writeConstraint(
                      fmt::format("(assert ((_ at-most 1)"));
                  for (auto s : tmp_var) {
                    SMTCell::writeConstraint(fmt::format(" {}", s));
                    SMTCell::cnt("l", 3);
                  }
                  SMTCell::writeConstraint(fmt::format("))\n"));
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

/**
 * Step Height Rule (SHR) rule:
 * Enforces avoiding “the small step” in SADP mask manufacturing.
 *
 * @note
 * Example: (SHR = 2) *Violation*
 * ====X====X----+---
 *     |    |    |
 * ====X----+----+---
 *     |    |    |
 * ====X====X----+---
 *
 * @param   SHR_Parameter   Distance in Graph
 * @param   doublePowerRail If using Double Power Rail
 *
 * @return  void
 */
void DesignRuleWriter::write_SHR_rule(int SHR_Parameter) {
  if (SHR_Parameter < 2) {
    fmt::print("is disable.....\n");
    SMTCell::writeConstraint(";SHR is disable\n");
  } else {
    // ### Paralle Run-Length Rule to prevent from having too close metal
    // tips.
    // ### DATA STRUCTURE:  VERTEX [index] [name] [Z-pos] [Y-pos] [X-pos]
    // [Arr. of adjacent vertices]
    // ### DATA STRUCTURE:  ADJACENT_VERTICES [0:Left] [1:Right] [2:Front]
    // [3:Back] [4:Up] [5:Down] [6:FL] [7:FR] [8:BL] [9:BR]
    if (SHR_Parameter == 0) {
      std::cout << "is disable\n";
      SMTCell::writeConstraint(";SHR is disable\n");
    } else {
      SMTCell::writeConstraint(
          ";13-A. from Right Tip to Right Tips for each vertex\n");
      DesignRuleWriter::write_SHR_R_tip_helper(SHR_Parameter);
      SMTCell::writeConstraint("\n");

      SMTCell::writeConstraint(
          ";13-B. from Left Tip to Left Tips for each vertex\n");
      DesignRuleWriter::write_SHR_L_tip_helper(SHR_Parameter);
      SMTCell::writeConstraint("\n");
      // ###### Skip to check exact adjacent GV variable, (From right to left
      // is enough), 11-B is executed when PRL_Parameter > 1
      SMTCell::writeConstraint(
          ";13-C. from Back Tip to Back Tips for each vertex\n");
      DesignRuleWriter::write_SHR_B_tip_helper(SHR_Parameter);
      SMTCell::writeConstraint("\n");
      SMTCell::writeConstraint(
          ";13-D. from Front Tip to Front Tips for each vertex\n");
      DesignRuleWriter::write_SHR_F_tip_helper(SHR_Parameter);
      SMTCell::writeConstraint("\n");
      fmt::print("have been written.\n");
    }
  }
}

/**
 * @note
 *                            ====+====X----X---- <--- BR Direction Checking
 *                                |    |    |
 *                            ▒▒▒▒X----+----+----
 *                                |    |    |
 *                            ====+====X----X---- <--- FR Direction Checking
 */
void DesignRuleWriter::write_SHR_R_tip_helper(int SHR_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) { // M2
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col < SMTCell::getRealNumTrackV() - step;
             col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }
          // # FR Direction Checking
          Triplet *vCoord_FR =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();

          if (SMTCell::ifVertex((*vCoord_FR)) == false) {
            continue;
          }

          if (vCoord_FR->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GR_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GR_V_{}", vCoord_FR->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_FR = SMTCell::getVertex((*vCoord_FR))->getRightADJ();
                // fmt::print("iterate {}", vCoord_FR)
                if (!vCoord_FR->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }

          // # BR Direction Checking
          Triplet *vCoord_BR = SMTCell::getVertex((*vCoord))->getBackRightADJ();

          if (SMTCell::ifVertex((*vCoord_BR)) == false) {
            continue;
          }

          if (vCoord_BR->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GR_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GR_V_{}", vCoord_BR->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_BR = SMTCell::getVertex((*vCoord_BR))->getRightADJ();
                if (!vCoord_BR->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 * BL Direction Checking ---> ----+----X====X====
 *                                |    |    |
 *                            ----+----+----X▒▒▒▒
 *                                |    |    |
 * FL Direction Checking ---> ----+----X====X====
 */
void DesignRuleWriter::write_SHR_L_tip_helper(int SHR_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 0) { // M2
      for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = step; col <= SMTCell::getRealNumTrackV() - 1;
             col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // # FL Direction Checking
          Triplet *vCoord_FL = SMTCell::getVertex((*vCoord))->getFrontLeftADJ();

          if (SMTCell::ifVertex((*vCoord_FL)) == false) {
            continue;
          }

          if (vCoord_FL->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GL_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GL_V_{}", vCoord_FL->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_FL = SMTCell::getVertex((*vCoord_FL))->getLeftADJ();
                // fmt::print("iterate {}", vCoord_FR)
                if (!vCoord_FL->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }

          // # BR Direction Checking
          Triplet *vCoord_BL = SMTCell::getVertex((*vCoord))->getBackLeftADJ();

          if (SMTCell::ifVertex((*vCoord_BL)) == false) {
            continue;
          }

          if (vCoord_BL->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GL_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GL_V_{}", vCoord_BL->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_BL = SMTCell::getVertex((*vCoord_BL))->getLeftADJ();
                if (!vCoord_BL->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 *                                |    |    |
 *                            ----+----+----+----
 *                                |    |    |
 * BL Direction Checking ---> ----X----+----X---- <--- BR Direction Checking
 *                                ║    |    ║
 *                            ----X----X----X----
 *                                ║    ▒    ║
 */
void DesignRuleWriter::write_SHR_B_tip_helper(int SHR_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer(); metal++) {
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 1) {
      for (int row = 0; row <= SMTCell::getNumTrackH() - 4; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1) {
          //   continue;
          // }
          if (metal > 1) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          Triplet *vCoord_BL =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();

          if (SMTCell::ifVertex((*vCoord_BL)) == false) {
            continue;
          }

          if (vCoord_BL->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GB_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GB_V_{}", vCoord_BL->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_BL = SMTCell::getVertex((*vCoord_BL))->getBackADJ();
                // fmt::print("iterate {}", vCoord_FR)
                if (!vCoord_BL->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }

          // # BR Direction Checking
          Triplet *vCoord_BR = SMTCell::getVertex((*vCoord))->getBackLeftADJ();

          if (SMTCell::ifVertex((*vCoord_BR)) == false) {
            continue;
          }

          if (vCoord_BR->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GB_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GB_V_{}", vCoord_BR->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_BR = SMTCell::getVertex((*vCoord_BR))->getBackADJ();
                if (!vCoord_BR->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}

/**
 * @note
 *                                ║    ▒    ║
 *                            ----X----X----X----
 *                                ║    |    ║
 * FL Direction Checking ---> ----X----+----X---- <--- FR Direction Checking
 *                                |    |    |
 *                            ----+----+----+----
 *                                |    |    |
 */
void DesignRuleWriter::write_SHR_F_tip_helper(int SHR_Parameter) {
  for (int metal = 2; metal <= SMTCell::getNumMetalLayer();
       metal++) { // no DR on M1
    int step = 0;
    if (metal == 1) {
      step = SMTCell::getMetalOneStep();
    } else if (metal >= 3) {
      step = SMTCell::getMetalThreeStep();
    } else {
      // # Metal 2 (M0)
      step = SMTCell::getGCDStep();
    }
    if (metal % 2 == 1) { // M2
      for (int row = 1; row <= SMTCell::getNumTrackH() - 3; row++) {
        for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1; col += step) {
          if (col % SMTCell::getMetalOneStep() != 0 &&
              col % SMTCell::getMetalThreeStep() != 0) {
            continue;
          }
          // if (metal > 1 && metal % 2 == 1) {
          //   continue;
          // }
          if (metal > 1) {
            continue;
          }
          Triplet *vCoord = new Triplet(metal, row, col);

          if (SMTCell::ifVertex((*vCoord)) == false) {
            continue;
          }

          // # Left-Front Direction
          Triplet *vCoord_FL = SMTCell::getVertex((*vCoord))->getFrontLeftADJ();

          if (SMTCell::ifVertex((*vCoord_FL)) == false) {
            continue;
          }

          if (vCoord_FL->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GL_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GL_V_{}", vCoord_FL->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_FL = SMTCell::getVertex((*vCoord_FL))->getFrontADJ();
                // fmt::print("iterate {}", vCoord_FR)
                if (!vCoord_FL->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }

          // # Right-Front Direction
          Triplet *vCoord_FR =
              SMTCell::getVertex((*vCoord))->getFrontRightADJ();

          if (SMTCell::ifVertex((*vCoord_FR)) == false) {
            continue;
          }

          if (vCoord_FR->ifValid()) {
            std::string tmp_str = "";
            std::vector<std::string> tmp_var;
            int cnt_var = 0;
            int cnt_true = 0;

            tmp_str = fmt::format("GL_V_{}", vCoord->getVname());

            // check declaration
            if (!SMTCell::ifAssigned(tmp_str)) {
              tmp_var.push_back(tmp_str);
              SMTCell::setVar(tmp_str, 2);
              cnt_var++;
            } else if (SMTCell::ifAssignedTrue(tmp_str)) {
              SMTCell::setVar_wo_cnt(tmp_str, 0);
              cnt_true++;
            }

            for (int shrIndex = 0; shrIndex <= SHR_Parameter - 2; shrIndex++) {
              tmp_str = fmt::format("GL_V_{}", vCoord_FR->getVname());

              // check declaration
              if (!SMTCell::ifAssigned(tmp_str)) {
                tmp_var.push_back(tmp_str);
                SMTCell::setVar(tmp_str, 2);
                cnt_var++;
              } else if (SMTCell::ifAssignedTrue(tmp_str)) {
                SMTCell::setVar_wo_cnt(tmp_str, 0);
                cnt_true++;
              }

              if (shrIndex != (SHR_Parameter - 2)) {
                // iterate to the right
                vCoord_FR = SMTCell::getVertex((*vCoord_FR))->getFrontADJ();
                if (!vCoord_FR->ifValid()) {
                  break;
                }
              }
            }

            if (cnt_true > 0) {
              if (cnt_true > 1) {
                fmt::print("[ERROR] SHR : more than one G Variables are "
                           "true!!!\n");
                exit(-1);
              } else {
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::assignTrueVar(tmp_var[i], 0, true);
                }
              }
            } else {
              if (cnt_var > 1) {
                SMTCell::writeConstraint("(assert ((_ at-most 1)");
                for (int i = 0; i < tmp_var.size(); i++) {
                  SMTCell::writeConstraint(fmt::format(" {}", tmp_var[i]));
                  SMTCell::cnt("l", 3);
                }
                SMTCell::writeConstraint("))\n");
                SMTCell::cnt("c", 3);
              }
            }
          }
        }
      }
    }
  }
}