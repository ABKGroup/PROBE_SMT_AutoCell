#include "placement.hpp"
#include "SMTCell.hpp"
#include "graph.hpp"
#include "obj.hpp"
#include <bitset>

namespace bmp = boost::multiprecision;

/**
 * Cost variables for PMOS and NMOS and total cost
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::init_cost_var(FILE *fp) {
  fmt::print(fp, "(declare-const COST_SIZE (_ BitVec {}))\n",
             SMTCell::getBitLengthNumTrackV());
  fmt::print(fp, "(declare-const COST_SIZE_P (_ BitVec {}))\n",
             SMTCell::getBitLengthNumTrackV());
  fmt::print(fp, "(declare-const COST_SIZE_N (_ BitVec {}))\n",
             SMTCell::getBitLengthNumTrackV());

  for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
    fmt::print(fp, "(declare-const M2_TRACK_{} Bool)\n", i);
  }

  // fix flag
  for (auto en : SMTCell::getExtNet()) {
    for (int i = 0; i < SMTCell::getNumTrackH() - 2; i++) {
      fmt::print(fp, "(declare-const N{}_M2_TRACK_{} Bool)\n", en.first, i);
    }
    fmt::print(fp, "(declare-const N{}_M2_TRACK Bool)\n", en.first);
  }
}

/**
 * Write max function to output file
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::write_max_func(FILE *fp) {
  fmt::print(
      fp,
      "(define-fun max ((x (_ BitVec {})) (y (_ BitVec {}))) (_ BitVec {})\n",
      SMTCell::getBitLengthNumTrackV(), SMTCell::getBitLengthNumTrackV(),
      SMTCell::getBitLengthNumTrackV());
  fmt::print(fp, "  (ite (bvsgt x y) x y)\n");
  fmt::print(fp, ")\n");
}

/**
 * Initialize placement variables for PMOS and NMOS
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::write_placement_var(FILE *fp) {
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    // instance x position
    fmt::print(fp, "(declare-const x{} (_ BitVec {}))\n", i,
               SMTCell::getBitLengthNumTrackV());
    SMTCell::cnt("v", 0);
    // instance flip flag
    fmt::print(fp, "(declare-const ff{} Bool)\n", i);
    SMTCell::cnt("v", 0);
    // instance y position
    fmt::print(fp, "(declare-const y{} (_ BitVec {}))\n", i,
               SMTCell::getBitLengthNumPTrackH());
    // unit width
    fmt::print(fp, "(declare-const uw{} (_ BitVec {}))\n", i,
               SMTCell::getBitLengthTrackEachPRow());
    // width
    fmt::print(fp, "(declare-const w{} (_ BitVec {}))\n", i,
               (bmp::msb(2 * tmp_finger[0] + 1) + 1));
    // num of finger
    // fmt::print("WHT {}\n", tmp_finger[0]);
    fmt::print(fp, "(declare-const nf{} (_ BitVec {}))\n", i,
               (bmp::msb(tmp_finger[0]) + 1));
  }
}

/**
 * Placement range constraints for PMOS and NMOS
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::write_placement_range_constr(FILE *fp) {
  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    int len = SMTCell::getBitLengthNumTrackV();
    // WARN FLAG: Ignore intermediate steps. Not used at all
    fmt::print(
        fp, "(assert (and (bvsge x{} (_ bv0 {})) (bvsle x{} (_ bv{} {}))))\n",
        i, len, i,
        std::to_string((SMTCell::getRealNumPTrackV() -
                        (2 * tmp_finger[0] + 1) * SMTCell::getMetalOneStep())),
        len);
    SMTCell::cnt("l", 0);
    SMTCell::cnt("l", 0);
    SMTCell::cnt("c", 0);
  }
}

/**
 * Set placement variables for PMOS
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::set_placement_var_pmos(FILE *fp) {
  for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());

    fmt::print(fp, "(assert (= y{} (_ bv{} {})))\n", i,
               (SMTCell::getNumPTrackH() -
                SMTCell::getInst(i)->getInstWidth() / tmp_finger[0]),
               SMTCell::getBitLengthNumPTrackH());

    fmt::print(fp, "(assert (= nf{} (_ bv{} {})))\n", i, tmp_finger[0],
               bmp::msb(tmp_finger[0]) + 1);

    fmt::print(fp, "(assert (= uw{} (_ bv{} {})))\n", i,
               SMTCell::getInst(i)->getInstWidth() / tmp_finger[0],
               SMTCell::getBitLengthTrackEachPRow());

    fmt::print(fp, "(assert (= w{} (_ bv{} {})))\n", i, (2 * tmp_finger[0] + 1),
               bmp::msb(2 * tmp_finger[0] + 1) + 1);
  }
}

/**
 * Set placement variables for NMOS
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::set_placement_var_nmos(FILE *fp) {
  for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getInstCnt(); i++) {
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());

    fmt::print(fp, "(assert (= y{} (_ bv0 {})))\n", i,
               SMTCell::getBitLengthNumPTrackH());

    fmt::print(fp, "(assert (= nf{} (_ bv{} {})))\n", i, tmp_finger[0],
               bmp::msb(tmp_finger[0]) + 1);

    fmt::print(fp, "(assert (= uw{} (_ bv{} {})))\n", i,
               SMTCell::getInst(i)->getInstWidth() / tmp_finger[0],
               SMTCell::getBitLengthTrackEachPRow());

    fmt::print(fp, "(assert (= w{} (_ bv{} {})))\n", i, (2 * tmp_finger[0] + 1),
               bmp::msb(2 * tmp_finger[0] + 1) + 1);
  }
}

/**
 * Gate on even columns and S/D on odd columns
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::write_bin_grid_constr(FILE *fp) {
  int len = SMTCell::getBitLengthNumTrackV();
  // convert to binary string
  std::string bin_grid = "";
  std::string bin_hgrid = "";
  if (len == 14) {
    bin_grid = std::bitset<14>(SMTCell::getMetalOneStep() * 2).to_string();
    bin_hgrid = std::bitset<14>(SMTCell::getMetalOneStep()).to_string();
  } else if (len == 15) {
    bin_grid = std::bitset<15>(SMTCell::getMetalOneStep() * 2).to_string();
    bin_hgrid = std::bitset<15>(SMTCell::getMetalOneStep()).to_string();
  } else if (len == 16) {
    bin_grid = std::bitset<16>(SMTCell::getMetalOneStep() * 2).to_string();
    bin_hgrid = std::bitset<16>(SMTCell::getMetalOneStep()).to_string();
  } else {
    fmt::print("[Error] Unkown bit length {} in setting bin grid\n", len);
    exit(1);
  }

  fmt::print(fp, "(declare-const grid (_ BitVec {}))\n", len);
  fmt::print(fp, "(declare-const hgrid (_ BitVec {}))\n", len);
  fmt::print(fp, "(assert (= grid #b{}))\n", bin_grid);
  fmt::print(fp, "(assert (= hgrid #b{}))\n", bin_hgrid);

  for (int i = 0; i < SMTCell::getInstCnt(); i++) {
    fmt::print(fp, "(assert (= (bvsmod x{} grid) hgrid))\n", i);
  }
}

/**
 * SDB/DDB
 * 
 * @param   *fp     output file pointer
 *
 * @return  void
 */
void Placement::write_XOL(FILE *fp, bool ifPMOS, int XOL_Mode,
                          int NDE_Parameter, int XOL_Parameter) {
  int startIdx = 0;
  int endIdx = 0;

  if (ifPMOS) {
    startIdx = 0;
    endIdx = SMTCell::getLastIdxPMOS() + 1;
  } else {
    startIdx = SMTCell::getLastIdxPMOS() + 1;
    endIdx = SMTCell::getInstCnt();
  }

  // line 1735
  // XOL Mode => 0: SDB, 1:DDB, 2:(Default)SDB/DDB mixed
  for (int i = startIdx; i < endIdx; i++) {
    // For instance i, retrieve pin IDs of source and drain
    int tmp_key_S_i =
        SMTCell::getInstWPinNetID(SMTCell::getInst(i)->getInstName() + "_S");
    int tmp_key_D_i =
        SMTCell::getInstWPinNetID(SMTCell::getInst(i)->getInstName() + "_D");
    std::vector<int> tmp_finger_i = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    int height_i = SMTCell::getInst(i)->getInstWidth() / tmp_finger_i[0];
    if (XOL_Mode > 0) {

      fmt::print(fp, "(declare-const fol_l_x{} Bool)\n", i);
      fmt::print(fp, "(declare-const fol_r_x{} Bool)\n", i);

      std::string tmp_str_xol_l = "(assert (ite (not (or";
      std::string tmp_str_xol_r = "(assert (ite (not (or";
      int cnt_xol = 0;

      for (int k = startIdx; k < endIdx; k++) {
        int len = SMTCell::getBitLengthNumTrackV();

        // for every pair of PMOS
        if (k != i) {
          // For instance k, retrieve pin IDs of source and drain
          int tmp_key_S_k = SMTCell::getInstWPinNetID(
              SMTCell::getInst(k)->getInstName() + "_S");
          int tmp_key_D_k = SMTCell::getInstWPinNetID(
              SMTCell::getInst(k)->getInstName() + "_D");
          std::vector<int> tmp_finger_k = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(k)->getInstWidth(), SMTCell::getTrackEachPRow());
          int height_k = SMTCell::getInst(k)->getInstWidth() / tmp_finger_k[0];

          if (NDE_Parameter == 0 && height_i != height_k) {
            continue;
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_k[0] % 2 == 0 &&
                     tmp_key_S_i != tmp_key_S_k) {
            continue;
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_k[0] % 2 == 1 &&
                     tmp_key_S_i != tmp_key_S_k && tmp_key_S_i != tmp_key_D_k) {
            continue;
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_k[0] % 2 == 0 &&
                     tmp_key_S_k != tmp_key_S_i && tmp_key_S_k != tmp_key_D_i) {
            continue;
          } else if (tmp_key_S_k != tmp_key_S_i && tmp_key_S_k != tmp_key_D_i &&
                     tmp_key_D_k != tmp_key_S_i && tmp_key_D_k != tmp_key_D_i) {
            continue;
          }

          fmt::print(fp,
                     "(assert (ite (= (bvadd x{} (_ bv{} {})) x{}) (= "
                     "fol_r_x{} true) (= #b1 #b1)))\n",
                     i, (2 * tmp_finger_i[0] * SMTCell::getMetalOneStep()), len,
                     k, i);
          fmt::print(fp,
                     "(assert (ite (= (bvsub x{} (_ bv{} {})) x{}) (= "
                     "fol_l_x{} true) (= #b1 #b1)))\n",
                     i, (2 * tmp_finger_k[0] * SMTCell::getMetalOneStep()), len,
                     k, i);
          tmp_str_xol_l +=
              " (= (bvadd x" + std::to_string(i) + " (_ bv" +
              std::to_string(2 * tmp_finger_i[0] * SMTCell::getMetalOneStep()) +
              " " + std::to_string(len) + ")) x" + std::to_string(k) + ")";
          tmp_str_xol_r +=
              " (= (bvsub x" + std::to_string(i) + " (_ bv" +
              std::to_string(2 * tmp_finger_k[0] * SMTCell::getMetalOneStep()) +
              " " + std::to_string(len) + ")) x" + std::to_string(k) + ")";
          cnt_xol++;
        }
      }
      tmp_str_xol_l +=
          ")) (= fol_r_x" + std::to_string(i) + " false) (= #b1 #b1)))\n";
      tmp_str_xol_r +=
          ")) (= fol_l_x" + std::to_string(i) + " false) (= #b1 #b1)))\n";

      if (cnt_xol > 0) {

        fmt::print(fp, "{}", tmp_str_xol_l);
        fmt::print(fp, "{}", tmp_str_xol_r);
      } else {
        fmt::print(fp, "(assert (= fol_r_x{} false))\n", i);
        fmt::print(fp, "(assert (= fol_l_x{} false))\n", i);
      }
    }

    for (int j = startIdx; j < endIdx; j++) {
      if (i != j) {
        // For instance i, retrieve pin IDs of source and drain
        int tmp_key_S_j = SMTCell::getInstWPinNetID(
            SMTCell::getInst(j)->getInstName() + "_S");
        int tmp_key_D_j = SMTCell::getInstWPinNetID(
            SMTCell::getInst(j)->getInstName() + "_D");
        std::vector<int> tmp_finger_j = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(j)->getInstWidth(), SMTCell::getTrackEachPRow());
        int height_j = SMTCell::getInst(j)->getInstWidth() / tmp_finger_j[0];

        int canShare = 1;
        if (NDE_Parameter == 0 && height_i != height_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0 &&
                   tmp_key_S_i != tmp_key_S_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1 &&
                   tmp_key_S_i != tmp_key_S_j && tmp_key_S_i != tmp_key_D_j) {
          canShare = 0;
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0 &&
                   tmp_key_S_j != tmp_key_S_i && tmp_key_S_j != tmp_key_D_i) {
          canShare = 0;
        } else if (tmp_key_S_j != tmp_key_S_i && tmp_key_S_j != tmp_key_D_i &&
                   tmp_key_D_j != tmp_key_S_i && tmp_key_D_j != tmp_key_D_i) {
          canShare = 0;
        }

        std::string tmp_str_ij;
        std::string tmp_str_ji;

        if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
          tmp_str_ij = "(= (_ bv" + std::to_string(tmp_key_S_i) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       ") (_ bv" + std::to_string(tmp_key_S_j) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       "))";
          tmp_str_ji = "(= (_ bv" + std::to_string(tmp_key_S_i) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       ") (_ bv" + std::to_string(tmp_key_S_j) + " " +
                       std::to_string(bmp::msb(SMTCell::getNumNetsOrg()) + 1) +
                       "))";
        } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_D_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ij.clear();
            } else {
              tmp_str_ij = "(= ff" + std::to_string(j) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
            } else {
              tmp_str_ij = "(= #b0 #b1)";
            }
          }
          // # nli = nrj
          if (tmp_key_S_i == tmp_key_S_j) {
            if (tmp_key_S_i == tmp_key_D_j) {
              tmp_str_ji.clear();
            } else {
              tmp_str_ji = "(= ff" + std::to_string(j) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_D_j) {
              tmp_str_ji = "(= ff" + std::to_string(j) + " false)";
            } else {
              tmp_str_ji = "(= #b0 #b1)";
            }
          }
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_S_j) {
            if (tmp_key_D_i == tmp_key_S_j) {
              tmp_str_ij.clear();
            } else {
              tmp_str_ij = "(= ff" + std::to_string(i) + " true)";
            }
          } else {
            if (tmp_key_D_i == tmp_key_S_j) {
              tmp_str_ij = "(= ff" + std::to_string(i) + " false)";
            } else {
              tmp_str_ij = "(= #b0 #b1)";
            }
          }
          // # nli = nrj
          if (tmp_key_D_i == tmp_key_S_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ji.clear();
            } else {
              tmp_str_ji = "(= ff" + std::to_string(i) + " true)";
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              tmp_str_ji = "(= ff" + std::to_string(i) + " false)";
            } else {
              tmp_str_ji = "(= #b0 #b1)";
            }
          }
        } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 1) {
          // # if nf % 2 == 1, if ff = 1 nl = $tmp_key_D, nr = $tmp_key_S
          // #                 if ff = 0 nl = $tmp_key_S, nr = $tmp_key_D
          // # nri = nlj
          if (tmp_key_S_i == tmp_key_D_j) {
            if (tmp_key_S_i == tmp_key_S_j) {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi = 0,1, ffj = 0,1
                  tmp_str_ij.clear();
                } else {
                  // ## ffi,ffj!=0 at the same time
                  tmp_str_ij = "(or (>= ff" + std::to_string(i) +
                               " true) (>= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ~(ffi=0 & ffj=1)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi = 1
                  tmp_str_ij = "(= ff" + std::to_string(i) + " true)";
                }
              }
            } else {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffj=1 or (ffi = 0 and ffj= 0)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " false)) (= ff" + std::to_string(j) + " true))";
                } else {
                  // ## ffj=1
                  tmp_str_ij = "(= ff" + std::to_string(j) + " true)";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi = ffj
                  tmp_str_ij = "(= ff" + std::to_string(i) + " ff" +
                               std::to_string(j) + ")";
                } else {
                  // ## ffi=1 and ffj=1
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " true))";
                }
              }
            }
          } else {
            if (tmp_key_S_i == tmp_key_S_j) {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## (ffi=0 and ffj=1) or ffj=0
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## (ffi=0 and ffj=1) or (ffi=1 and ffj=0)
                  tmp_str_ij = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false)))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffj =0
                  tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=1 and ffj=0
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false))";
                }
              }
            } else {
              if (tmp_key_D_i == tmp_key_D_j) {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi=0
                  tmp_str_ij = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=0 and ffj=1
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_D_i == tmp_key_S_j) {
                  // ## ffi=0 and ffj=0
                  tmp_str_ij = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi=0 and ffj=0
                  tmp_str_ij = "(= #b1 #b0)";
                }
              }
            }
          }

          // # nli = nrj
          if (tmp_key_D_i == tmp_key_S_j) {
            if (tmp_key_D_i == tmp_key_D_j) {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi = 0,1, ffj = 0,1
                  tmp_str_ji.clear();
                } else {
                  // ## ffi,ffj!=0 at the same time
                  tmp_str_ji = "(or (>= ff" + std::to_string(i) +
                               " true) (>= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ~(ffi=0 & ffj=1)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi = 1
                  tmp_str_ji = "(= ff" + std::to_string(i) + " true)";
                }
              }
            } else {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffj=1 or (ffi = 0 and ffj= 0)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " false)) (= ff" + std::to_string(j) + " true))";
                } else {
                  // ## ffj=1
                  tmp_str_ji = "(= ff" + std::to_string(j) + " true)";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi = ffj
                  tmp_str_ji = "(= ff" + std::to_string(i) + " ff" +
                               std::to_string(j) + ")";
                } else {
                  // ## ffi=1 and ffj=1
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " true))";
                }
              }
            }
          } else {
            if (tmp_key_D_i == tmp_key_D_j) {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## (ffi=0 and ffj=1) or ffj=0
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## (ffi=0 and ffj=1) or (ffi=1 and ffj=0)
                  tmp_str_ji = "(or (and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) +
                               " true)) (and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false)))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffj =0
                  tmp_str_ji = "(= ff" + std::to_string(i) + " false)";
                } else {
                  // ## ffi=1 and ffj=0
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " true) (= ff" + std::to_string(j) + " false))";
                }
              }
            } else {
              if (tmp_key_S_i == tmp_key_S_j) {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi=0
                  tmp_str_ji = "(= ff" + std::to_string(j) + " false)";
                } else {
                  // ## ffi=0 and ffj=1
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " true))";
                }
              } else {
                if (tmp_key_S_i == tmp_key_D_j) {
                  // ## ffi=0 and ffj=0
                  tmp_str_ji = "(and (= ff" + std::to_string(i) +
                               " false) (= ff" + std::to_string(j) + " false))";
                } else {
                  // ## ffi=0 and ffj=0
                  tmp_str_ji = "(= #b1 #b0)";
                }
              }
            }
          }
        }

        int len = SMTCell::getBitLengthNumTrackV();
        std::string f_wi =
            "(_ bv" +
            std::to_string(2 * tmp_finger_i[0] * SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";
        std::string f_wj =
            "(_ bv" +
            std::to_string(2 * tmp_finger_j[0] * SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";
        std::string xol =
            "(_ bv" +
            std::to_string(XOL_Parameter * SMTCell::getMetalOneStep()) + " " +
            std::to_string(len) + ")";
        std::string xol_i =
            "(_ bv" +
            std::to_string((2 * tmp_finger_i[0] + XOL_Parameter) *
                           SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";
        std::string xol_j =
            "(_ bv" +
            std::to_string((2 * tmp_finger_j[0] + XOL_Parameter) *
                           SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";
        std::string xol_i_o =
            "(_ bv" +
            std::to_string((2 * tmp_finger_i[0] + XOL_Parameter - 2) *
                           SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";
        std::string xol_j_o =
            "(_ bv" +
            std::to_string((2 * tmp_finger_j[0] + XOL_Parameter - 2) *
                           SMTCell::getMetalOneStep()) +
            " " + std::to_string(len) + ")";

        int tmp_idx = 0;

        if (ifPMOS) {
          tmp_idx = SMTCell::getLastIdxPMOS();
        } else {
          if (NDE_Parameter == 1) {
            height_i = height_j;
          }
          tmp_idx =
              SMTCell::getNumInstance() - 1 - SMTCell::getLastIdxPMOS() - 1;
        }

        if (XOL_Mode > 0 && tmp_idx >= 2) {
          fmt::print(fp,
                     "(assert (ite (and fol_r_x{} (bvslt (bvadd x{} {}) x{})) "
                     "(bvsle (bvadd x{} {}) x{})\n",
                     i, i, f_wi, j, i, xol_i_o, j);

          if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
            // # sourses of both inst are the same => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o, j);
            }
            // # sources of both inst are different => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
            // # source of inst i is same as source and drain of inst j => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, i, i, xol_i_o, j);
            }
            // # source of inst i is same as source of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i is same as drain of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
            // # source of inst j is same as source and drain of inst i => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_j == tmp_key_S_i && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o);
            }

            // # source of inst j is same as source of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source of inst j is same as drain of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          } else {
            // # all source/drain are the same ==> SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_D_i && tmp_key_S_j == tmp_key_D_j &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i_o, j);
            }
            // # source/drain of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source/drain of inst i && drain of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, j, xol_i_o, xol_i, j);
            }
            // # source/drain of inst j && source of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite ff{} {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source/drain of inst j && drain of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, xol_i_o, xol_i, j);
            }
            // # source of inst i && source of inst j, drain of inst i && drain
            // of inst j are the same => conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j && tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (or (and (not ff{}) ff{}) (and ff{} "
                         "(not ff{}))) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && drain of inst j, drain of inst i && source
            // of inst j are the same => coinditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j && tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (or (and (not ff{}) (not ff{})) (and "
                         "ff{} ff{})) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and ff{} (not ff{})) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # source of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and ff{} ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # drain of inst i && source of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_S_j) {
              fmt::print(
                  fp,
                  "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle (bvadd "
                  "x{} (ite (and (not ff{}) (not ff{})) {} {})) x{})\n",
                  i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // # drain of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_D_j) {
              // fmt::print("\n\t FLAG 1 \t\n");
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} (ite (and (not ff{}) ff{}) {} {})) x{})\n",
                         i, f_wi, j, i, i, j, xol_i_o, xol_i, j);
            }
            // DDB
            else {
              fmt::print(fp,
                         "		(ite (bvslt (bvadd x{} {}) x{}) (bvsle "
                         "(bvadd x{} {}) x{})\n",
                         i, f_wi, j, i, xol_i, j);
            }
          }

          if (canShare == 1) {
            fmt::print(fp,
                       "		(ite (and (= (bvadd x{} {}) x{}) {}) "
                       "(= (bvadd x{} {}) x{})\n",
                       i, f_wi, j, tmp_str_ij, i, f_wi, j);
          }

          fmt::print(fp,
                     "		(ite (and fol_l_x{} (bvsgt (bvsub x{} {}) "
                     "x{})) (bvsge (bvsub x{} {}) x{})\n",
                     i, i, f_wj, j, i, xol_j_o, j);
          if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 0) {
            // # sourses of both inst are the same => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                (tmp_key_S_i == tmp_key_S_j)) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # sources of both inst are different => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else if (tmp_finger_i[0] % 2 == 0 && tmp_finger_j[0] % 2 == 1) {
            // # source of inst i is same as source and drain of inst j => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_S_j && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source of inst i is same as source of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i is same as drain of inst j => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else if (tmp_finger_i[0] % 2 == 1 && tmp_finger_j[0] % 2 == 0) {
            // # source of inst j is same as source and drain of inst i => SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_j == tmp_key_S_i && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source of inst j is same as source of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source of inst j is same as drain of inst i => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # no source/drain is same between inst i/j => DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          } else {
            // fmt::print("\n\t FLAG 2 outer {}, {}, {}\t\n", tmp_key_S_i,
            //            tmp_key_S_j,
            //            (XOL_Mode == 2 &&
            //             (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //             tmp_key_S_i == tmp_key_S_j));
            // if (!(XOL_Mode == 2 &&
            //      (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
            //      tmp_key_S_i == tmp_key_S_j)) {
            //   fmt::print("\n\t FLAG 2 inner {}, {}, {}\t\n", (XOL_Mode == 2),
            //              (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)),
            //              (tmp_key_S_i == tmp_key_S_j));
            // }
            // line 2289
            // # all source/drain are the same ==> SDB
            if (XOL_Mode == 2 &&
                (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                tmp_key_S_i == tmp_key_D_i && tmp_key_S_j == tmp_key_D_j &&
                tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j_o, j);
            }
            // # source/drain of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source/drain of inst i && drain of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_i && tmp_key_S_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, j, xol_j_o, xol_j, j);
            }
            // # source/drain of inst j && source of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_S_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (not ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source/drain of inst j && drain of inst i are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_j == tmp_key_D_j && tmp_key_S_j == tmp_key_D_i) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite ff{} {} {})) x{})\n",
                         i, f_wj, j, i, i, xol_j_o, xol_j, j);
            }
            // # source of inst i && source of inst j, drain of inst i && drain
            // of inst j are the same => conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j && tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (or (and (not ff{}) ff{}) (and ff{} "
                         "(not ff{}))) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && drain of inst j, drain of inst i && source
            // of inst j are the same => coinditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j && tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (or (and (not ff{}) (not ff{})) (and "
                         "ff{} ff{})) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && source of inst j are the same =>
            // conditional SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_S_j) {
              // fmt::print("\n\t FLAG 2 \t\n");
              fmt::print(
                  fp,
                  "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                  "x{} (ite (and (not ff{}) ff{}) {} {})) x{})\n",
                  i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # source of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_S_i == tmp_key_D_j) {
              fmt::print(
                  fp,
                  "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                  "x{} (ite (and (not ff{}) (not ff{})) {} {})) x{})\n",
                  i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # drain of inst i && source of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_S_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (and ff{} ff{}) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # drain of inst i && drain of inst j are the same => conditional
            // SDB/DDB
            else if (XOL_Mode == 2 &&
                     (SMTCell::ifSDBInst(i) && SMTCell::ifSDBInst(j)) &&
                     tmp_key_D_i == tmp_key_D_j) {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} (ite (and ff{} (not ff{})) {} {})) x{})\n",
                         i, f_wj, j, i, i, j, xol_j_o, xol_j, j);
            }
            // # DDB
            else {
              fmt::print(fp,
                         "		(ite (bvsgt (bvsub x{} {}) x{}) (bvsge "
                         "(bvsub x{} {}) x{})\n",
                         i, f_wj, j, i, xol_j, j);
            }
          }

          if (canShare == 1) {
            fmt::print(fp,
                       "		(ite (and (= (bvsub x{} {}) x{}) {}) "
                       "(= (bvsub x{} {}) x{})\n",
                       i, f_wj, j, tmp_str_ji, i, f_wj, j);
          }

          if (canShare == 1) {
            fmt::print(fp, "		(= #b1 #b0))))))))\n");
          } else {
            fmt::print(fp, "		(= #b1 #b0))))))\n");
          }

        } else {
          if (canShare == 1) {

            fmt::print(fp,
                       "(assert (ite (bvslt (bvadd x{} {}) x{}) (bvsle (bvadd "
                       "x{} {}) x{})\n",
                       i, f_wi, j, i, xol_i, j);
            fmt::print(fp,
                       "        (ite (and (= (bvadd x{} {}) x{}) {}) (= (bvadd "
                       "x{} {}) x{})\n",
                       i, f_wi, j, tmp_str_ij, i, f_wi, j);
            fmt::print(fp,
                       "        (ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, i, xol_j, j);
            fmt::print(fp,
                       "        (ite (and (= (bvsub x{} {}) x{}) {}) (= (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, tmp_str_ji, i, f_wj, j);
            fmt::print(fp, "        (= #b1 #b0))))))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);

          } else {

            fmt::print(fp,
                       "(assert (ite (bvslt (bvadd x{} {}) x{}) (bvsle (bvadd "
                       "x{} {}) x{})\n",
                       i, f_wi, j, i, xol_i, j);
            fmt::print(fp,
                       "        (ite (bvsgt (bvsub x{} {}) x{}) (bvsge (bvsub "
                       "x{} {}) x{})\n",
                       i, f_wj, j, i, xol_j, j);
            fmt::print(fp, "        (= #b1 #b0))))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);
          }
        }
      }
    }
  }
}

/**
 * Cost function for Gate metal
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::set_default_G_metal() {
  std::map<const std::string, int> h_tmp;
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
           vEdgeIndex++) {
        // ignoring $virtualEdges[$vEdgeIndex][2] =~ /^pin/ since this is
        // always a pin name
        VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
        std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string sinkPin =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        if (tmp_ve->getPinName() == sourcePin) {
          Pin *pin_s = SMTCell::getPin(sourcePin);
          // external net should NOT be considered
          if (pin_s->getInstID() == "ext") {
            continue;
          }
          // instance index
          int instIdx = SMTCell::getPinInstIdx(pin_s);
          std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
              SMTCell::getInst(instIdx)->getInstWidth(),
              SMTCell::getTrackEachPRow());

          // fixed value, should be variable
          int height = SMTCell::getRealTrackHeight();

          // Source pin is Gate
          if (SMTCell::getPin(sourcePin)->getPinType() == "G") {
            // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
            int tmp_col = tmp_ve->getVCoord()->col_;
            if (SMTCell::ifGCol(tmp_col)) {
              // vertex name in Metal variables
              // ignored tmp_vname as it is not used anywhere
              // bug found: need DEEP COPY for ptr objects
              Triplet *tmp_vname_first = new Triplet();
              Triplet *tmp_vname_second = new Triplet();
              std::memcpy(tmp_vname_first, tmp_ve->getVCoord(),
                          sizeof(Triplet));
              std::memcpy(tmp_vname_second, tmp_ve->getVCoord(),
                          sizeof(Triplet));
              // tmp_vname_first = tmp_ve->getVCoord();
              // tmp_vname_second = tmp_ve->getVCoord();
              // PMOS
              if (instIdx <= SMTCell::getLastIdxPMOS()) {
                for (int i = 0; i <= height - 2; i++) {
                  int j = i;
                  int k = j + 1;
                  // fmt::print("#1 j={}, k={}\n", j, k);
                  // mergeable#4077
                  tmp_vname_first->setRow(j);
                  tmp_vname_second->setRow(k);
                  // write to constraint
                  const std::string metal_variable =
                      fmt::format("M_{}_{}", tmp_vname_first->getVname(),
                                  tmp_vname_second->getVname());
                  if (h_tmp.find(metal_variable) == h_tmp.end()) {
                    if (!SMTCell::ifAssigned(metal_variable)) {
                      // fmt::print("1 {}\n", metal_variable);
                      SMTCell::setVar(metal_variable, 2);
                      SMTCell::writeConstraint(fmt::format(
                          "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= {} "
                          "true) (= {} false)))\n",
                          (tmp_col > 0 ? (tmp_col - SMTCell::getMetalOneStep())
                                       : tmp_col),
                          SMTCell::getBitLengthNumTrackV(), metal_variable,
                          metal_variable));
                      h_tmp[metal_variable] = 1;
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("c", 1);
                    }
                  }
                }
              } else {
                // NMOS
                for (int i = 0; i <= height - 2; i++) {
                  int j = SMTCell::getNumTrackH() - 2 - height + i;
                  int k = j + 1;
                  // fmt::print("#2 j={}, k={}\n", j, k);
                  // mergeable#4077
                  tmp_vname_first->setRow(j);
                  tmp_vname_second->setRow(k);
                  // write to constraint
                  std::string metal_variable =
                      fmt::format("M_{}_{}", tmp_vname_first->getVname(),
                                  tmp_vname_second->getVname());
                  if (h_tmp.find(metal_variable) == h_tmp.end()) {
                    if (!SMTCell::ifAssigned(metal_variable)) {
                      // fmt::print("2 {}\n", metal_variable);
                      SMTCell::setVar(metal_variable, 2);
                      SMTCell::writeConstraint(fmt::format(
                          "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= {} "
                          "true) (= {} false)))\n",
                          (tmp_col > 0 ? (tmp_col - SMTCell::getMetalOneStep())
                                       : tmp_col),
                          SMTCell::getBitLengthNumTrackV(), metal_variable,
                          metal_variable));
                      h_tmp[metal_variable] = 1;
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("l", 1);
                      SMTCell::cnt("c", 1);
                    }
                  }
                }
              }
            }
          }
        } else if (tmp_ve->getPinName() == sinkPin) {
          if (tmp_ve->getPinName() != Pin::keySON) {
            Pin *pin_t = SMTCell::getPin(sinkPin);
            // external net should NOT be considered
            if (pin_t->getInstID() == "ext") {
              continue;
            }
            // instance index
            int instIdx = SMTCell::getPinInstIdx(pin_t);
            std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
                SMTCell::getInst(instIdx)->getInstWidth(),
                SMTCell::getTrackEachPRow());

            // fixed value, should be variable
            int height = SMTCell::getRealTrackHeight();

            // Source pin is Gate
            if (SMTCell::getPin(sourcePin)->getPinType() == "G") {
              // VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
              int tmp_col = tmp_ve->getVCoord()->col_;
              if (SMTCell::ifGCol(tmp_col)) {
                // vertex name in Metal variables
                // ignored tmp_vname as it is not used anywhere
                // bug found: need DEEP COPY for ptr objects
                Triplet *tmp_vname_first = new Triplet();
                Triplet *tmp_vname_second = new Triplet();
                std::memcpy(tmp_vname_first, tmp_ve->getVCoord(),
                            sizeof(Triplet));
                std::memcpy(tmp_vname_second, tmp_ve->getVCoord(),
                            sizeof(Triplet));
                // PMOS
                if (instIdx <= SMTCell::getLastIdxPMOS()) {
                  for (int i = 0; i < height - 1; i++) {
                    int j = i;
                    int k = j + 1;
                    // fmt::print("#3 j={}, k={}\n", j, k);
                    // mergeable#4077
                    tmp_vname_first->setRow(j);
                    tmp_vname_second->setRow(k);
                    // write to constraint
                    const std::string metal_variable =
                        fmt::format("M_{}_{}", tmp_vname_first->getVname(),
                                    tmp_vname_second->getVname());
                    if (h_tmp.find(metal_variable) == h_tmp.end()) {
                      if (!SMTCell::ifAssigned(metal_variable)) {
                        SMTCell::setVar(metal_variable, 2);
                        SMTCell::writeConstraint(fmt::format(
                            "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                            "{} "
                            "true) (= {} false)))\n",
                            (tmp_col > 0
                                 ? (tmp_col - SMTCell::getMetalOneStep())
                                 : tmp_col),
                            SMTCell::getBitLengthNumTrackV(), metal_variable,
                            metal_variable));
                        h_tmp[metal_variable] = 1;
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("c", 1);
                      }
                    }
                  }
                } else {
                  // NMOS
                  for (int i = 0; i < height - 1; i++) {
                    int j = SMTCell::getNumTrackH() - 2 - height + i;
                    int k = j + 1;
                    // fmt::print("#4 j={}, k={}\n", j, k);
                    // mergeable#4077
                    tmp_vname_first->setRow(j);
                    tmp_vname_second->setRow(k);
                    // write to constraint
                    const std::string metal_variable =
                        fmt::format("M_{}_{}", tmp_vname_first->getVname(),
                                    tmp_vname_second->getVname());
                    if (h_tmp.find(metal_variable) == h_tmp.end()) {
                      if (!SMTCell::ifAssigned(metal_variable)) {
                        SMTCell::setVar(metal_variable, 2);
                        SMTCell::writeConstraint(fmt::format(
                            "(assert (ite (bvsge COST_SIZE (_ bv{} {})) (= "
                            "{} "
                            "true) (= {} false)))\n",
                            (tmp_col > 0
                                 ? (tmp_col - SMTCell::getMetalOneStep())
                                 : tmp_col),
                            SMTCell::getBitLengthNumTrackV(), metal_variable,
                            metal_variable));
                        h_tmp[metal_variable] = 1;
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("l", 1);
                        SMTCell::cnt("c", 1);
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

/**
 * Right most metals are not used given device width
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::unset_rightmost_metal() {
  // fmt::print(" MOS min width: {}\n", SMTCell::getMOSMinWidth());
  SMTCell::writeConstraint(";Unset All Metal/Net/Wire over the rightmost "
                           "cell/metal(>COST_SIZE+1)\n");

  // # Unset All Metal/Net/Wire over the rightmost cell/metal(>COST_SIZE+1)
  // line 3399
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
    int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
    int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
    int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
    if (fromMetal == toMetal && fromMetal == 1) {
      continue;
    }

    // this could equal to 2 because min possible width is 2 * 1 (# fingers)
    // if (SMTCell::getMOSMinWidth() > 2 &&
    //     toCol > SMTCell::getMOSMinWidth() - 2) {
    if (SMTCell::getMOSMinWidth() >= 2 &&
        toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
      if (!SMTCell::ifAssigned(variable_name)) {
        SMTCell::setVar(variable_name, 2);
        // SMTCell::writeConstraint(fmt::format(
        //     "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
        //     "false) (= true true)))\n",
        //     (toCol - 2), SMTCell::getBitLengthNumTrackV(), variable_name));
        SMTCell::writeConstraint(
            fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                        "false) (= true true)))\n",
                        (toCol - 1 * SMTCell::getMetalOneStep()),
                        SMTCell::getBitLengthNumTrackV(), variable_name));
        SMTCell::cnt("l", 1);
        SMTCell::cnt("l", 1);
        SMTCell::cnt("c", 1);
      }
    }
    // why? you need to store it in h_assign
    if (fromMetal == toMetal && fromMetal == 3) {
      if (toCol == 0 && fromCol == 0) {
        SMTCell::writeConstraint(fmt::format(
            "(assert (= M_{}_{} false))\n",
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname()));
      }
    }
  }

  // SMTCell::dump_h_assign();

  // line 3417
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
         udEdgeIndex++) {
      int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
      int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
      int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
      int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
      int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
      int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
      if (fromMetal == toMetal && fromMetal == 1) {
        continue;
      }
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol >
              (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
        std::string variable_name = fmt::format(
            "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
            SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
        if (!SMTCell::ifAssigned(variable_name)) {
          SMTCell::setVar(variable_name, 2);
          SMTCell::writeConstraint(
              fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                          "false) (= true true)))\n",
                          (toCol - 1 * SMTCell::getMetalOneStep()),
                          SMTCell::getBitLengthNumTrackV(), variable_name));
          SMTCell::cnt("l", 1);
          SMTCell::cnt("l", 1);
          SMTCell::cnt("c", 1);
        }
      }

      if (fromMetal == toMetal && fromMetal == 3) {
        if (toCol == 0 && fromCol == 0) {
          SMTCell::writeConstraint(fmt::format(
              "(assert (= N{}_E_{}_{} false))\n",
              SMTCell::getNet(netIndex)->getNetID(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
              SMTCell::getUdEdge(udEdgeIndex)
                  ->getUdToEdge()
                  ->getVname()));
        }
      }
    }
  }

  // line 3438
  SMTCell::writeConstraint(";line 3438 \n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        // fmt::print("{} {} {}\n", netIndex, commodityIndex, udEdgeIndex);
        int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
        int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
        int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
        int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
        if (fromMetal == toMetal && fromMetal == 1) {
          continue;
        }
        // fmt::print("HERE! minWidth {} toCol {} \n",
        // SMTCell::getMOSMinWidth(),
        //            toCol);
        if (SMTCell::getMOSMinWidth() >= 2 &&
            toCol >
                (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
          // missing N1 C1 here
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex,
              SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
          // if (SMTCell::getNet(netIndex)->getNetID() == "1") {
          //   fmt::print("HERE! {} Ifassigned? {}\n", variable_name,
          //              SMTCell::ifAssigned(variable_name));
          // }
          // bug found previously assigned
          if (!SMTCell::ifAssigned(variable_name)) {
            // fmt::print("HERE!\n");
            SMTCell::setVar(variable_name, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                            "false) (= true true)))\n",
                            (toCol - (1 * SMTCell::getMetalOneStep())),
                            SMTCell::getBitLengthNumTrackV(), variable_name));
            SMTCell::cnt("l", 1);
            SMTCell::cnt("l", 1);
            SMTCell::cnt("c", 1);
          }
        }

        // why? you need to store it in h_assign
        if (fromMetal == toMetal && fromMetal == 3) {
          if (toCol == 0 && fromCol == 0) {
            SMTCell::writeConstraint(
                fmt::format("(assert (= N{}_E_{}_{} false))\n",
                            SMTCell::getNet(netIndex)->getNetID(),
                            SMTCell::getUdEdge(udEdgeIndex)
                                ->getUdFromEdge()
                                ->getVname(),
                            SMTCell::getUdEdge(udEdgeIndex)
                                ->getUdToEdge()
                                ->getVname()));
          }
        }
      }
    }
  }

  // SMTCell::writeConstraint("; has issue flag ^\n");
  // line 3462
  for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
       vEdgeIndex++) {
    int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
    if (SMTCell::getMOSMinWidth() > 2 &&
        toCol > (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->getVname(),
          SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
      if (!SMTCell::ifAssigned(variable_name)) {
        SMTCell::setVar(variable_name, 2);
        SMTCell::writeConstraint(
            fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                        "false) (= true true)))\n",
                        (toCol - (2 * SMTCell::getMetalOneStep())),
                        SMTCell::getBitLengthNumTrackV(), variable_name));
        SMTCell::cnt("l", 1);
        SMTCell::cnt("l", 1);
        SMTCell::cnt("c", 1);
      }
    }
  }

  // line 3475
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
         vEdgeIndex++) {
      int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol >
              (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
        VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
        std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
        // Source pin
        if (tmp_ve->getPinName() == sourcePin) {
          std::string variable_name = fmt::format(
              "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              tmp_ve->getVCoord()->getVname(), tmp_ve->getPinName());
          if (!SMTCell::ifAssigned(variable_name)) {
            SMTCell::setVar(variable_name, 2);
            SMTCell::writeConstraint(
                fmt::format("(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                            "false) (= true true)))\n",
                            (toCol - (2 * SMTCell::getMetalOneStep())),
                            SMTCell::getBitLengthNumTrackV(), variable_name));
            SMTCell::cnt("l", 1);
            SMTCell::cnt("l", 1);
            SMTCell::cnt("c", 1);
          }
        } else {
          // Sink pin
          for (int commodityIndex = 0;
               commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
               commodityIndex++) {
            std::string sinkPin =
                SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
            if (tmp_ve->getPinName() == sinkPin) {
              std::string variable_name = fmt::format(
                  "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  tmp_ve->getVCoord()->getVname(), tmp_ve->getPinName());
              if (!SMTCell::ifAssigned(variable_name)) {
                SMTCell::setVar(variable_name, 2);
                SMTCell::writeConstraint(fmt::format(
                    "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                    "false) (= true true)))\n",
                    (toCol - (2 * SMTCell::getMetalOneStep())),
                    SMTCell::getBitLengthNumTrackV(), variable_name));
                SMTCell::cnt("l", 1);
                SMTCell::cnt("l", 1);
                SMTCell::cnt("c", 1);
              }
            }
          }
        }
      }
    }
  }

  // line 3505
  SMTCell::writeConstraint(";line 3505 \n");
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
         vEdgeIndex++) {
      VirtualEdge *tmp_ve = SMTCell::getVirtualEdge(vEdgeIndex);
      int toCol = tmp_ve->getVCoord()->col_;
      // ignored metals since not used
      if (SMTCell::getMOSMinWidth() >= 2 &&
          toCol >
              (SMTCell::getMOSMinWidth() - 2) * SMTCell::getMetalOneStep()) {
        for (int commodityIndex = 0;
             commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
             commodityIndex++) {
          std::string sourcePin = SMTCell::getNet(netIndex)->getSource_ofNet();
          std::string sinkPin =
              SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, tmp_ve->getVCoord()->getVname(),
              tmp_ve->getPinName());
          if (tmp_ve->getPinName() == sourcePin) {
            // if (!SMTCell::ifAssigned(variable_name)) {
            //   SMTCell::setVar(variable_name, 2);
            //   SMTCell::writeConstraint(fmt::format(
            //       "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
            //       "false) (= true true)))\n",
            //       (toCol - 2), SMTCell::getBitLengthNumTrackV(),
            //       variable_name));
            //   SMTCell::cnt("l", 1);
            //   SMTCell::cnt("l", 1);
            //   SMTCell::cnt("c", 1);
            // }
          }
          if (tmp_ve->getPinName() == sinkPin) {
            if (!SMTCell::ifAssigned(variable_name)) {
              SMTCell::setVar(variable_name, 2);
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (bvsle COST_SIZE (_ bv{} {})) (= {} "
                  "false) (= true true)))\n",
                  (toCol - 2 * SMTCell::getMetalOneStep()),
                  SMTCell::getBitLengthNumTrackV(), variable_name));
              SMTCell::cnt("l", 1);
              SMTCell::cnt("l", 1);
              SMTCell::cnt("c", 1);
            }
          }
        }
      }
    }
  }
}

/**
 * Adjacent pins of the same FET should be placed in the same region
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::localize_adjacent_pin(int local_Parameter) {
  int step = 0;
  if (local_Parameter == 1) {
    SMTCell::writeConstraint(";Localization.\n\n");
    SMTCell::writeConstraint(
        ";Localization for Adjacent Pins in the same multifinger TRs.\n\n");
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // inst pin idx
        std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        // external net should NOT be considered
        // if (pidx_s == Pin::keySON || pidx_t == Pin::keySON) {
        //   continue;
        // }
        // pin ptr
        Pin *pin_s = SMTCell::getPin(pidx_s);
        Pin *pin_t = SMTCell::getPin(pidx_t);
        // external net should NOT be considered
        // if (pin_s->getInstID() == "ext" || pin_t->getInstID() == "ext") {
        //   continue;
        // }
        // inst idx
        int inst_pin_s = SMTCell::getPinInstIdx(pin_s);
        int inst_pin_t = SMTCell::getPinInstIdx(pin_t);
        // type
        // std::string type_s = pin_s->getPinType();
        // std::string type_t = pin_t->getPinType();
        // finger
        // std::vector<int> finger_s = SMTCell::getAvailableNumFinger(
        //     SMTCell::getInst(inst_pin_s)->getInstWidth(),
        //     SMTCell::getTrackEachPRow());
        // std::vector<int> finger_t = SMTCell::getAvailableNumFinger(
        //     SMTCell::getInst(inst_pin_t)->getInstWidth(),
        //     SMTCell::getTrackEachPRow());
        // width
        // int w_s = finger_s[0] * 2;
        // int w_t = finger_t[0] * 2;
        int len = SMTCell::getBitLengthNumTrackV();
        // h_edge is never initalized, ignored for now
        // skip if target is SON
        // pidx_s = std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"),
        // "$1"); pidx_t = std::regex_replace(pidx_t,
        // std::regex("pin\\S+_(\\d+)"), "$1");
        if (pidx_t != Pin::keySON) {
          // skip if s/t same inst
          if (inst_pin_s == inst_pin_t) {
            for (int metal = 3; metal <= SMTCell::getNumMetalLayer(); metal++) {
              if (metal == 1) {
                step = SMTCell::getMetalOneStep();
              } else if (metal >= 3) {
                step = SMTCell::getMetalThreeStep();
              } else {
                // # Metal 2 (M0)
                step = SMTCell::getGCDStep();
              }
              for (int col = 0; col <= SMTCell::getRealNumTrackV() - 1;
                   col += step) {
                if (col % SMTCell::getMetalOneStep() != 0 &&
                    col % SMTCell::getMetalThreeStep() != 0) {
                  continue;
                }
                for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
                  // if (metal > 1 && metal % 2 == 1 && col % 2 == 1) {
                  //   continue;
                  // }
                  Triplet vCoord = Triplet(metal, row, col);
                  // fmt::print("vCoord: {}\n", vCoord.getVname());
                  // incoming
                  if (SMTCell::ifEdgeIn(vCoord.getVname())) {
                    for (int i : SMTCell::getEdgeIn(vCoord.getVname())) {
                      std::string variable_name = fmt::format(
                          "N{}_C{}_E_{}_{}",
                          SMTCell::getNet(netIndex)->getNetID(), commodityIndex,
                          SMTCell::getUdEdge(i)
                              ->getUdFromEdge()
                              ->getVname(),
                          vCoord.getVname());

                      // fmt::print("{}\n", variable_name);
                      // SMTCell::assignTrueVar(variable_name, 0, false);
                      // SMTCell::assignTrueVar(
                      //     SMTCell::getNet(netIndex)->getNetID(),
                      //     commodityIndex, SMTCell::getUdEdge(i)
                      //         ->getUdFromEdge()
                      //         ->getVname(),
                      //     vCoord.getVname(), 0, false);
                      // fmt::print("{}\n", variable_name);
                      SMTCell::assignFalseVar(variable_name);
                    }
                  }

                  if (SMTCell::ifEdgeOut(vCoord.getVname())) {
                    // outgoing
                    for (int i : SMTCell::getEdgeOut(vCoord.getVname())) {
                      std::string variable_name =
                          fmt::format("N{}_C{}_E_{}_{}",
                                      SMTCell::getNet(netIndex)->getNetID(),
                                      commodityIndex, vCoord.getVname(),
                                      SMTCell::getUdEdge(i)
                                          ->getUdToEdge()
                                          ->getVname());
                      // fmt::print("{}\n", variable_name);
                      // SMTCell::assignTrueVar(variable_name, 0, false);
                      // SMTCell::assignTrueVar(
                      //     SMTCell::getNet(netIndex)->getNetID(),
                      //     commodityIndex, vCoord.getVname(),
                      //     SMTCell::getUdEdge(i)
                      //         ->getUdToEdge()
                      //         ->getVname(),
                      //     0, false);
                      // fmt::print("{}\n", variable_name);
                      SMTCell::assignFalseVar(variable_name);
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

/**
 * Remove symmetric placement case
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::remove_symmetric_placement(FILE *fp, bool BS_Parameter) {
  if (BS_Parameter == 1) {
    fmt::print(fp, ";Removing Symmetric Placement Cases\n");
    int numPMOS = SMTCell::getLastIdxPMOS() + 1;
    int numNMOS = SMTCell::getNumInstance() - numPMOS;
    std::vector<int> arr_pmos;
    std::vector<int> arr_nmos;

    // fmt::print("PMOS: {}\n", numPMOS);
    // fmt::print("NMOS: {}\n", numNMOS);

    for (int i = 0; i < SMTCell::getLastIdxPMOS() + 1; i++) {
      arr_pmos.push_back(i);
    }

    // fmt::print("arr_pmos\n");
    // for (int i = 0; i < arr_pmos.size(); i++) {
    //   fmt::print("{}\n", arr_pmos[i]);
    // }

    for (int i = SMTCell::getLastIdxPMOS() + 1; i < SMTCell::getNumInstance();
         i++) {
      arr_nmos.push_back(i);
    }

    std::vector<std::vector<int>> comb_l_pmos = {};
    std::vector<std::vector<int>> comb_l_nmos = {};
    std::vector<std::vector<int>> comb_c_pmos = {};
    std::vector<std::vector<int>> comb_c_nmos = {};
    std::vector<std::vector<int>> comb_r_pmos = {};
    std::vector<std::vector<int>> comb_r_nmos = {};

    // PMOS
    if (numPMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_pmos =
          SMTCell::combine(arr_pmos, numPMOS / 2);
      for (int i = 0; i < tmp_comb_l_pmos.size(); i++) {
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            for (int k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
              if (tmp_comb_l_pmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        // avoid SEGFAULT
        if (tmp_comb_l_pmos.size() > i) {
          comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
        }
        comb_r_pmos.push_back(tmp_comb);
        if (tmp_comb_l_pmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = 0; m < numPMOS; m++) {
        arr_pmos.clear();

        for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
          if (i != m) {
            arr_pmos.push_back(i);
          }
        }

        std::vector<std::vector<int>> tmp_comb_l_pmos =
            SMTCell::combine(arr_pmos, (numPMOS - 1) / 2);

        // for (auto f : tmp_comb_l_pmos) {
        //   fmt::print("  [\n");
        //   for (auto fr : f) {
        //     fmt::print("    {}\n", fr);
        //   }
        //   fmt::print("  ]\n");
        // }

        for (int i = 0; i < tmp_comb_l_pmos.size(); i++) {
          // fmt::print("i: {} {}\n", i, tmp_comb_l_pmos.size());
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_pmos.size() > i) {
              for (int k = 0; k < tmp_comb_l_pmos[i].size(); k++) {
                if (tmp_comb_l_pmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }

          // avoid SEGFAULT
          if (tmp_comb_l_pmos.size() > i) {
            comb_l_pmos.push_back(tmp_comb_l_pmos[i]);
          }
          comb_r_pmos.push_back(tmp_comb);
          comb_c_pmos.push_back({m});

          if (tmp_comb_l_pmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    // NMOS
    if (numNMOS % 2 == 0) {
      std::vector<std::vector<int>> tmp_comb_l_nmos =
          SMTCell::combine(arr_nmos, numNMOS / 2);
      for (int i = 0; i < tmp_comb_l_nmos.size(); i++) {
        std::vector<int> tmp_comb;
        int isComb = 0;
        for (int j = SMTCell::getLastIdxPMOS() + 1;
             j < SMTCell::getNumInstance(); ++j) {
          // check vec size to prevent SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            for (int k = 0; k < tmp_comb_l_nmos[i].size(); ++k) {
              if (tmp_comb_l_nmos[i][k] == j) {
                isComb = 1;
                break;
              }
            }
          }
          if (isComb == 0) {
            tmp_comb.push_back(j);
          }
          isComb = 0;
        }
        if (tmp_comb_l_nmos.size() > i) {
          comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
        }
        comb_r_nmos.push_back(tmp_comb);
        if (tmp_comb_l_nmos.size() - 1 == 1) {
          break;
        }
      }
    } else {
      for (int m = SMTCell::getLastIdxPMOS() + 1; m < SMTCell::getNumInstance();
           m++) {
        arr_nmos.clear();

        for (int i = 0; i < numNMOS; i++) {
          if (i + SMTCell::getLastIdxPMOS() + 1 != m) {
            arr_nmos.push_back(i + SMTCell::getLastIdxPMOS() + 1);
          }
        }

        std::vector<std::vector<int>> tmp_comb_l_nmos =
            SMTCell::combine(arr_nmos, (numNMOS - 1) / 2);

        for (int i = 0; i < tmp_comb_l_nmos.size(); i++) {
          std::vector<int> tmp_comb;
          int isComb = 0;
          for (int j = SMTCell::getLastIdxPMOS() + 1;
               j < SMTCell::getNumInstance(); j++) {
            // avoid SEGFAULT
            if (tmp_comb_l_nmos.size() > i) {
              for (int k = 0; k < tmp_comb_l_nmos[i].size(); k++) {
                if (tmp_comb_l_nmos[i][k] == j || j == m) {
                  isComb = 1;
                  break;
                }
              }
            }
            if (isComb == 0) {
              tmp_comb.push_back(j);
            }
            isComb = 0;
          }
          // avoid SEGFAULT
          if (tmp_comb_l_nmos.size() > i) {
            comb_l_nmos.push_back(tmp_comb_l_nmos[i]);
          }
          comb_r_nmos.push_back(tmp_comb);
          comb_c_nmos.push_back({m});

          if (tmp_comb_l_nmos.size() - 1 == 1) {
            break;
          }
        }
      }
    }

    // print size of comb_l_pmos
    // fmt::print("; comb_l_pmos.size() = {}\n", comb_l_pmos.size());
    // fmt::print("; comb_r_pmos.size() = {}\n", comb_l_pmos.size());
    // fmt::print("; comb_c_pmos.size() = {}\n", comb_l_pmos.size());

    // fmt::print("; comb_l_nmos.size() = {}\n", comb_l_nmos.size());
    // fmt::print("; comb_r_nmos.size() = {}\n", comb_r_nmos.size());
    // fmt::print("; comb_c_nmos.size() = {}\n", comb_c_nmos.size());

    for (int i = 0; i < comb_l_pmos.size(); ++i) {
      fmt::print(fp, "(assert (or");

      if (comb_l_pmos.size() <= i) {
        continue;
      } // prevent segfault

      for (int l = 0; l < comb_l_pmos[i].size(); ++l) {
        if (comb_r_pmos.size() <= i) {
          continue;
        } // prevent segfault
        for (int m = 0; m < comb_r_pmos[i].size(); ++m) {
          fmt::print(fp, " (bvslt x{} x{})", comb_l_pmos[i][l],
                     comb_r_pmos[i][m]);
          SMTCell::cnt("l", 0);

          if (comb_c_pmos.size() <= i) {
            continue;
          } // prevent segfault
          // fmt::print("{}\n", i);
          for (int n = 0; n < comb_c_pmos[i].size(); ++n) {
            fmt::print(fp, " (bvslt x{} x{})", comb_l_pmos[i][l],
                       comb_c_pmos[i][n]);
            fmt::print(fp, " (bvsgt x{} x{})", comb_r_pmos[i][m],
                       comb_c_pmos[i][n]);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
          }
        }
      }
      fmt::print(fp, " (and");

      for (int j = 0; j < comb_l_nmos.size(); ++j) {
        fmt::print(fp, " (or");
        if (comb_l_nmos.size() <= i) {
          continue;
        } // prevent segfault

        for (int l = 0; l < comb_l_nmos[j].size(); ++l) {
          if (comb_r_nmos.size() <= i) {
            continue;
          } // prevent segfault
          for (int m = 0; m < comb_r_nmos[j].size(); ++m) {
            fmt::print(fp, " (bvslt x{} x{})", comb_l_nmos[j][l],
                       comb_r_nmos[j][m]);
            SMTCell::cnt("l", 0);

            if (comb_c_nmos.size() <= i) {
              continue;
            } // prevent segfault
            // fmt::print("{}\n", j);
            for (int n = 0; n < comb_c_nmos[j].size(); ++n) {
              fmt::print(fp, " (bvslt x{} x{})", comb_l_nmos[j][l],
                         comb_c_nmos[j][n]);
              fmt::print(fp, " (bvsgt x{} x{})", comb_r_nmos[j][m],
                         comb_c_nmos[j][n]);
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }
          }
        }
        fmt::print(fp, ")");
      }
      fmt::print(fp, ")))\n");
      SMTCell::cnt("c", 0);
    }
    fmt::print(fp, ";Set flip status to false for FETs which have even "
                   "numbered fingers\n");
    for (int i = 0; i <= SMTCell::getLastIdxPMOS(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    for (int i = SMTCell::getNumPMOS(); i < SMTCell::getNumInstance(); i++) {
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      if (tmp_finger[0] % 2 == 0) {
        fmt::print(fp, "(assert (= ff{} false))\n", i);
        SMTCell::cnt("l", 0);
        SMTCell::cnt("c", 0);
      }
    }
    fmt::print(fp, ";End of Symmetric Removal\n");
  }
}

/**
 * Initialize Value for Gate Pins of P/N FET in the same column
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::init_placement_G_pin() {
  SMTCell::writeConstraint(
      ";Set Initial Value for Gate Pins of P/N FET in the same column\n");
  // ## Set Initial Value for Gate Pins of P/N FET in the same column
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      std::string tmp_vname = "";
      // inst pin idx
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::string pidx_t =
          SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);

      // external net should NOT be considered
      if (pidx_s == Pin::keySON || pidx_t == Pin::keySON) {
        continue;
      }

      // ignore startIdx and endIdx, not used
      Pin *source_pin = SMTCell::getPin(pidx_s);
      Pin *sink_pin = SMTCell::getPin(pidx_t);

      // external net should NOT be considered
      if (source_pin->getInstID() == "ext" || sink_pin->getInstID() == "ext") {
        continue;
      }

      // ## Source MaxFlow Indicator
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // ## Sink MaxFlow Indicator
      int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

      // finger
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(sink_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      // ## Skip If Source/Sink TR is in the same region
      if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
           sink_inst_idx <= SMTCell::getLastIdxPMOS()) ||
          (source_inst_idx > SMTCell::getLastIdxPMOS() &&
           sink_inst_idx > SMTCell::getLastIdxPMOS())) {
        continue;
      }

      int row_s = 0;
      int row_t = 0;
      // if Source inst is PMOS
      if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
        row_s = 0;
      } else {
        row_s = SMTCell::getNumTrackH() - 3;
      }

      // if Sink inst is PMOS
      if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
        row_t = 0;
      } else {
        row_t = SMTCell::getNumTrackH() - 3;
      }

      // ## Skip if Source/Sink Pin is not "Gate" Pin
      if (source_pin->getPinType() != "G" || sink_pin->getPinType() != "G") {
        continue;
      }

      int tmp_pidx_s = std::stoi(
          std::regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
      int tmp_pidx_t = std::stoi(
          std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));

      for (int col = SMTCell::getMetalOneStep();
           col < SMTCell::getRealNumTrackV();
           col += SMTCell::getMetalOneStep()) {

        int len = SMTCell::getBitLengthNumTrackV();
        std::string tmp_str = "";
        std::vector<std::string> tmp_var_T;
        std::vector<std::string> tmp_var_F;
        int cnt_var_T = 0;
        int cnt_var_F = 0;

        Triplet vCoord;
        // P3 FLAG
        if (SMTCell::ifGCol(col)) {
          // fmt::print("col = {}\n", col);
          // # Variables to Set True
          // Source
          vCoord = Triplet(1, row_s, col);
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord.getVname(), pidx_s);
          tmp_var_T.push_back(variable_name);
          SMTCell::setVar(variable_name, 2);
          cnt_var_T++;

          vCoord = {}; // reset

          // Sink
          vCoord = Triplet(1, row_t, col);
          variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord.getVname(), pidx_t);
          tmp_var_T.push_back(variable_name);
          SMTCell::setVar(variable_name, 2);
          cnt_var_T++;

          for (int row = 0; row <= SMTCell::getNumTrackH() - 4; row++) {
            Triplet vCoord_1 = Triplet(1, row, col);
            Triplet vCoord_2 = Triplet(1, (row + 1), col);
            variable_name = fmt::format(
                "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                commodityIndex, vCoord_1.getVname(), vCoord_2.getVname());
            tmp_var_T.push_back(variable_name);
            SMTCell::setVar(variable_name, 2);
            cnt_var_T++;
          }

          // # Variables to Set False
          for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
               udEdgeIndex++) {
            int fromCol =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
            int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
            int fromRow =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
            int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
            int fromMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
            int toMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;

            if (fromMetal == 1 || toMetal == 1) {
              int step = SMTCell::getMetalOneStep();
            } else {
              int step = SMTCell::getMetalThreeStep();
            }

            if (!(fromMetal == 1 && toMetal == 1 && fromCol == toCol &&
                  fromCol == col)) {
              variable_name = fmt::format("N{}_C{}_E_{}_{}",
                                          SMTCell::getNet(netIndex)->getNetID(),
                                          commodityIndex,
                                          SMTCell::getUdEdge(udEdgeIndex)
                                              ->getUdFromEdge()
                                              ->getVname(),
                                          SMTCell::getUdEdge(udEdgeIndex)
                                              ->getUdToEdge()
                                              ->getVname());
              if (!SMTCell::ifAssigned(variable_name)) {
                tmp_var_F.push_back(variable_name);
                SMTCell::setVar(variable_name, 2);
                cnt_var_F++;
              }
            }
          }

          for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
               vEdgeIndex++) {
            int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
            if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() == pidx_s ||
                SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() == pidx_t) {
              if (toCol > col || toCol < col) {
                variable_name = fmt::format(
                    "M_{}_{}",
                    SMTCell::getVirtualEdge(vEdgeIndex)
                        ->getVCoord()
                        ->getVname(),
                    SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
                if (!SMTCell::ifAssigned(variable_name)) {
                  tmp_var_F.push_back(variable_name);
                  SMTCell::setVar(variable_name, 2);
                  cnt_var_F++;
                }
              }
            }
          }

          // fmt::print("col: {}, tmp_pidx_s: {}, tmp_pidx_t: {}\n", col,
          //            tmp_pidx_s, tmp_pidx_t);
          if (cnt_var_T > 0 || cnt_var_F > 0) {
            if (col - tmp_pidx_s * SMTCell::getMetalOneStep() > 0 &&
                col - tmp_pidx_t * SMTCell::getMetalOneStep() > 0) {
              SMTCell::writeConstraint(fmt::format(
                  "(assert (ite (and (= x{} (_ bv{} {})) (= x{} "
                  "(_ bv{} {})))",
                  source_inst_idx,
                  (col - tmp_pidx_s * SMTCell::getMetalOneStep()), len,
                  sink_inst_idx,
                  (col - tmp_pidx_t * SMTCell::getMetalOneStep()), len));
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
              SMTCell::writeConstraint(" (and");
              for (int m = 0; m < tmp_var_T.size(); m++) {
                SMTCell::writeConstraint(
                    fmt::format(" (= {} true)", tmp_var_T[m]));
                SMTCell::cnt("l", 1);
              }

              for (int m = 0; m < tmp_var_F.size(); m++) {
                SMTCell::writeConstraint(
                    fmt::format(" (= {} false)", tmp_var_F[m]));
                SMTCell::cnt("l", 1);
              }

              SMTCell::writeConstraint(") (= 1 1)))\n");
              SMTCell::cnt("c", 1);
            }
          }
        }
      }
    }
  }
}

/**
 * Initialize Value for overlapped S/D Pins of P/N FET in the same column
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::init_placement_overlap_SD_pin() {
  SMTCell::writeConstraint(";Set Initial Value for overlapped S/D Pins of "
                           "Each P/N FET Region in the same column\n");
  // ## Set Initial Value for overlapped S/D Pins of Each P/N FET Region in
  // the same column
  for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
    for (int commodityIndex = 0;
         commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
         commodityIndex++) {
      std::string tmp_vname = "";
      // inst pin idx
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      std::string pidx_t =
          SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);

      // external net should NOT be considered
      if (pidx_s == Pin::keySON || pidx_t == Pin::keySON) {
        continue;
      }

      int startIdx = 0;
      int endIdx_s = 0;
      int endIdx_t = 0;

      Pin *source_pin = SMTCell::getPin(pidx_s);
      Pin *sink_pin = SMTCell::getPin(pidx_t);

      // external net should NOT be considered
      if (source_pin->getInstID() == "ext" || sink_pin->getInstID() == "ext") {
        continue;
      }

      // ## Source MaxFlow Indicator
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // ## Sink MaxFlow Indicator
      int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

      // finger
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(sink_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      // ## Skip If Source/Sink TR is in the different region
      if ((source_inst_idx <= SMTCell::getLastIdxPMOS() &&
           sink_inst_idx > SMTCell::getLastIdxPMOS()) ||
          (source_inst_idx > SMTCell::getLastIdxPMOS() &&
           sink_inst_idx <= SMTCell::getLastIdxPMOS())) {
        continue;
      }

      int row_s = 0;
      int row_t = 0;

      // if Source inst is PMOS
      if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
        row_s = 0;
      } else {
        row_s = SMTCell::getNumTrackH() - 3;
      }

      // if Sink inst is PMOS
      if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
        row_t = 0;
      } else {
        row_t = SMTCell::getNumTrackH() - 3;
      }

      // ## Skip if Source/Sink Pin is "Gate" Pin
      if (source_pin->getPinType() == "G" || sink_pin->getPinType() == "G") {
        continue;
      }

      int tmp_pidx_s =
          std::stoi(regex_replace(pidx_s, std::regex("pin\\S+_(\\d+)"), "$1"));
      int tmp_pidx_t = std::stoi(
          std::regex_replace(pidx_t, std::regex("pin\\S+_(\\d+)"), "$1"));

      // ## Skip if each pin is not the left/rightmost pin
      if (tmp_pidx_s > 0 && tmp_pidx_s < tmp_finger_source[0] * 2) {
        continue;
      }
      if (tmp_pidx_t > 0 && tmp_pidx_t < tmp_finger_sink[0] * 2) {
        continue;
      }

      for (int col = SMTCell::getMetalOneStep();
           col < SMTCell::getRealNumTrackV();
           col += SMTCell::getMetalOneStep()) {
        int len = SMTCell::getBitLengthNumTrackV();
        std::string tmp_str = "";
        std::vector<std::string> tmp_var_T;
        std::vector<std::string> tmp_var_F;
        int cnt_var_T = 0;
        int cnt_var_F = 0;

        Triplet vCoord;
        if (SMTCell::ifSDCol(col)) {
          // # Variables to Set True
          // Source
          vCoord = Triplet(1, row_s, col);
          std::string variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord.getVname(), pidx_s);
          tmp_var_T.push_back(vCoord.getVname());
          SMTCell::setVar(variable_name, 2);
          cnt_var_T++;

          vCoord = {}; // reset

          // Sink
          vCoord = Triplet(1, row_t, col);
          variable_name = fmt::format(
              "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
              commodityIndex, vCoord.getVname(), pidx_t);
          tmp_var_T.push_back(vCoord.getVname());
          SMTCell::setVar(variable_name, 2);
          cnt_var_T++;

          // # Variables to Set False
          for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
               udEdgeIndex++) {
            int fromCol =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
            int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
            int fromRow =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
            int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
            int fromMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
            int toMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
            int step = 0;
            if (fromMetal == 1 || toMetal == 1) {
              step = SMTCell::getMetalOneStep();
            } else {
              step = SMTCell::getMetalThreeStep();
            }
            variable_name = fmt::format("N{}_C{}_E_{}_{}",
                                        SMTCell::getNet(netIndex)->getNetID(),
                                        commodityIndex,
                                        SMTCell::getUdEdge(udEdgeIndex)
                                            ->getUdFromEdge()
                                            ->getVname(),
                                        SMTCell::getUdEdge(udEdgeIndex)
                                            ->getUdToEdge()
                                            ->getVname());
            if (!SMTCell::ifAssigned(variable_name)) {
              tmp_var_F.push_back(variable_name);
              SMTCell::setVar(variable_name, 2);
              cnt_var_F++;
            }
          }

          for (int vEdgeIndex = 0; vEdgeIndex < SMTCell::getVirtualEdgeCnt();
               vEdgeIndex++) {
            // ignore toRow, not used
            int toCol = SMTCell::getVirtualEdge(vEdgeIndex)->getVCoord()->col_;
            if (SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() == pidx_s ||
                SMTCell::getVirtualEdge(vEdgeIndex)->getPinName() == pidx_t) {
              if (toCol > col || toCol < col) {
                variable_name = fmt::format(
                    "M_{}_{}",
                    SMTCell::getVirtualEdge(vEdgeIndex)
                        ->getVCoord()
                        ->getVname(),
                    SMTCell::getVirtualEdge(vEdgeIndex)->getPinName());
                if (!SMTCell::ifAssigned(variable_name)) {
                  tmp_var_F.push_back(variable_name);
                  SMTCell::setVar(variable_name, 2);
                  cnt_var_F++;
                }
              }
            }
          }

          if (cnt_var_T > 0 || cnt_var_F > 0) {
            startIdx = 0;
            endIdx_s = tmp_finger_source[0] * 2 + 1;
            endIdx_t = tmp_finger_sink[0] * 2 + 1;
            SMTCell::writeConstraint("(assert (ite (and");

            int isValid = 0;

            if (tmp_pidx_s * SMTCell::getMetalOneStep() <= col) {
              isValid = 1;
              SMTCell::writeConstraint(fmt::format(
                  " (or (and (= ff{} false) (= x{} (_ bv{} {})))",
                  source_inst_idx, source_inst_idx,
                  (col - tmp_pidx_s * SMTCell::getMetalOneStep()), len));
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }

            int tmp_col = (((startIdx + endIdx_s - 1 - tmp_pidx_s) % 2 == 0
                                ? (startIdx + endIdx_s - 1 - tmp_pidx_s) *
                                      SMTCell::getMetalOneStep()
                                : (startIdx + endIdx_s - 1 - tmp_pidx_s + 1) *
                                      SMTCell::getMetalOneStep()));

            if (tmp_col <= col) {
              if (isValid == 0) {
                SMTCell::writeConstraint(
                    fmt::format(" (or (and (= ff{} true)", source_inst_idx));
                SMTCell::cnt("l", 0);
                isValid = 1;
              } else {
                SMTCell::writeConstraint(
                    fmt::format(" (and (= ff{} true)", source_inst_idx));
                SMTCell::cnt("l", 0);
              }

              int len = SMTCell::getBitLengthNumTrackV();
              SMTCell::writeConstraint(fmt::format(" (= x{} (_ bv{} {})))",
                                                   source_inst_idx,
                                                   (col - tmp_col), len));
              SMTCell::cnt("l", 0);
            }

            if (isValid == 0) {
              continue;
            }

            SMTCell::writeConstraint(")");
            isValid = 0;
            if (tmp_pidx_t * SMTCell::getMetalOneStep() <= col) {
              isValid = 1;
              SMTCell::writeConstraint(fmt::format(
                  " (or (and (= ff{} false) (= x{} (_ bv{} {})))",
                  sink_inst_idx, sink_inst_idx,
                  (col - tmp_pidx_t * SMTCell::getMetalOneStep()), len));
              SMTCell::cnt("l", 0);
              SMTCell::cnt("l", 0);
            }

            tmp_col = (((startIdx + endIdx_t - 1 - tmp_pidx_t) % 2 == 0
                            ? (startIdx + endIdx_t - 1 - tmp_pidx_t) *
                                  SMTCell::getMetalOneStep()
                            : (startIdx + endIdx_t - 1 - tmp_pidx_t + 1) *
                                  SMTCell::getMetalOneStep()));

            if (tmp_col <= col) {
              if (isValid == 0) {
                SMTCell::writeConstraint(
                    fmt::format(" (or (and (= ff{} true)", sink_inst_idx));
                SMTCell::cnt("l", 0);
                isValid = 1;
              } else {
                SMTCell::writeConstraint(
                    fmt::format(" (and (= ff{} true)", sink_inst_idx));
                SMTCell::cnt("l", 0);
              }

              int len = SMTCell::getBitLengthNumTrackV();
              SMTCell::writeConstraint(fmt::format(" (= x{} (_ bv{} {})))",
                                                   sink_inst_idx,
                                                   (col - tmp_col), len));
              SMTCell::cnt("l", 0);
            }

            if (isValid == 0) {
              continue;
            }

            SMTCell::writeConstraint(")");
            SMTCell::writeConstraint(") (and");

            // potential bug, not writing out T, why?
            for (int m = 0; m < tmp_var_T.size(); m++) {
              // SMTCell::writeConstraint(
              //     fmt::format(" (= {} true)", tmp_var_T[m]));
              SMTCell::cnt("l", 1);
            }

            for (int m = 0; m < tmp_var_F.size(); m++) {
              SMTCell::writeConstraint(
                  fmt::format(" (= {} false)", tmp_var_F[m]));
              SMTCell::cnt("l", 1);
            }

            SMTCell::writeConstraint(") (= 1 1)))\n");
            SMTCell::cnt("c", 1);
          }
        }
      }
    }
  }
}

/**
 * Initialize Instance into different partition groups
 * 
 * @param   void
 *
 * @return  void
 */
void Placement::init_InstPartition(int Partition_Parameter) {
  if (Partition_Parameter != 2) {
    return;
  }
  SMTCell::sortInstPartition();
  int prev_group_p = -1;
  int prev_group_n = -1;

  std::vector<int> tmp_p_array;
  std::vector<int> tmp_n_array;

  int minWidth_p = 0;
  int minWidth_n = 0;
  int ifRemain_p = 0;
  int ifRemain_n = 0;

  for (int i = 0; i < SMTCell::getInstPartitionCnt(); i++) {
    // if PMOS
    if (SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)) <=
        SMTCell::getLastIdxPMOS()) {
      // flush prev group
      if (prev_group_p != -1 &&
          prev_group_p != SMTCell::getInstPartitionGroup(i)) {
        // initialize an vector with h_inst_idx in it
        // sort tmp_p_array in ascending order
        std::sort(tmp_p_array.begin(), tmp_p_array.end());
        SMTCell::addInstPartitionPMOS(prev_group_p, tmp_p_array, minWidth_p);
        // clear tmp_p_array
        tmp_p_array.clear();
        minWidth_p = 0;
      }
      prev_group_p = SMTCell::getInstPartitionGroup(i);
      tmp_p_array.push_back(
          SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)));

      ifRemain_p = 1;

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(
              SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)))
              ->getInstWidth(),
          SMTCell::getTrackEachPRow());
      minWidth_p += 2 * tmp_finger[0];

      // print previous group
      // fmt::print(" {} ", SMTCell::getInstPartitionName(i));
    } else {
      // if NMOS
      // flush prev group
      if (prev_group_n != -1 &&
          prev_group_n != SMTCell::getInstPartitionGroup(i)) {
        // initialize an vector with h_inst_idx in it
        // sort tmp_n_array in ascending order
        std::sort(tmp_p_array.begin(), tmp_p_array.end());
        SMTCell::addInstPartitionNMOS(prev_group_n, tmp_n_array, minWidth_n);
        // clear tmp_p_array
        tmp_n_array.clear();
        minWidth_n = 0;
      }
      prev_group_n = SMTCell::getInstPartitionGroup(i);
      tmp_n_array.push_back(
          SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)));
      ifRemain_n = 1;

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(
              SMTCell::getInstIdx(SMTCell::getInstPartitionName(i)))
              ->getInstWidth(),
          SMTCell::getTrackEachPRow());

      minWidth_n += 2 * tmp_finger[0];
    }
  }

  if (ifRemain_p == 1) {
    SMTCell::addInstPartitionPMOS(prev_group_p, tmp_p_array, minWidth_p);
  }

  if (ifRemain_n == 1) {
    SMTCell::addInstPartitionNMOS(prev_group_n, tmp_n_array, minWidth_n);
  }
};

/**
 * Special Net Constraint for disabling track assignment to certain nets
 * 
 * @param   ML_Parameter Min Metal Length for avoiding adjacent signal routing
 *
 * @return  void
 */
void Placement::write_special_net_constraint(int ML_Parameter) {
  int numTrackAssign = SMTCell::getSpNetCnt();
  if (numTrackAssign > 0) {
    SMTCell::writeConstraint(";Set Net Track Assignment Constraints\n");
    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
        int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
        if (toMetal == 4) {
          // # Assigned Net && unassigned track => Disable Track Variables
          // except for the assigned tracks
          // this is the same as
          // !exists($h_net_track{"$nets[$netIndex][1]\_$fromRow"})
          if (SMTCell::ifSpNet(netIndex) &&
              !SMTCell::ifSpTrackNet(fromRow, netIndex)) {
            // fmt::print("net {} fromRow {} udEdgeIndex {}\n", netIndex,
            // fromRow,
            //            udEdgeIndex);
            std::string variable_name = fmt::format(
                "N{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                SMTCell::getUdEdge(udEdgeIndex)
                    ->getUdFromEdge()
                    ->getVname(),
                SMTCell::getUdEdge(udEdgeIndex)
                    ->getUdToEdge()
                    ->getVname());
            if (!SMTCell::ifAssigned(variable_name)) {
              SMTCell::setVar(variable_name, 2);
              SMTCell::writeConstraint(
                  fmt::format("(assert (= {} false))\n", variable_name));
              SMTCell::cnt("l", 1);
              SMTCell::cnt("l", 1);
              SMTCell::cnt("c", 1);
            }
          }
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
             udEdgeIndex++) {
          int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
          int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
          int fromMetal =
              SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
          int toMetal =
              SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
          if (toMetal == 4) {
            // # Assigned Net && unassigned track => Disable Track Variables
            // except for the assigned tracks
            if (SMTCell::ifSpNet(netIndex) &&
                !SMTCell::ifSpTrackNet(fromRow, netIndex)) {
              std::string variable_name = fmt::format(
                  "N{}_C{}_E_{}_{}", SMTCell::getNet(netIndex)->getNetID(),
                  commodityIndex,
                  SMTCell::getUdEdge(udEdgeIndex)
                      ->getUdFromEdge()
                      ->getVname(),
                  SMTCell::getUdEdge(udEdgeIndex)
                      ->getUdToEdge()
                      ->getVname());

              if (!SMTCell::ifAssigned(variable_name)) {
                SMTCell::setVar(variable_name, 2);
                SMTCell::writeConstraint(
                    fmt::format("(assert (= {} false))\n", variable_name));
                SMTCell::cnt("l", 1);
                SMTCell::cnt("l", 1);
                SMTCell::cnt("c", 1);
              }
            }
          }
        }
      }
    }

    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      std::vector<std::string> tmp_track_nets;
      if (SMTCell::ifSpTrack(row)) {
        tmp_track_nets = SMTCell::getSpTrackNet(row);
        if (tmp_track_nets.size() == 0) {
          continue;
        }

        int cnt_var = 0;
        std::string tmp_str;
        for (int udEdgeIndex; udEdgeIndex < SMTCell::getUdEdgeCnt();
             udEdgeIndex++) {
          for (int i = 0; i < tmp_track_nets.size(); i++) {
            std::string netIndex = tmp_track_nets[i];
            int fromRow =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
            int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
            int fromMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
            int toMetal =
                SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;

            if (toMetal == 4 && fromRow == row) {
              std::string variable_name =
                  fmt::format("N{}_E_{}_{}", netIndex,
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdFromEdge()
                                  ->getVname(),
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdToEdge()
                                  ->getVname());
              if (!SMTCell::ifAssigned(variable_name)) {
                SMTCell::setVar(variable_name, 2);
                tmp_str += " " + variable_name;
                cnt_var++;
              }
            }
          }
          if (cnt_var > 1) {
            SMTCell::writeConstraint(
                fmt::format("(assert ((_ at-most 1){}))\n", tmp_str));
          }
        }
      }
    }
  }
  SMTCell::writeConstraint(";End of Net Track Assignment Constraints\n");
}

/**
 * Encode partition groups constraints
 * 
 * @param   Partition_Parameter   whether to enable partition constraints
 *
 * @return  void
 */
void Placement::write_partition_constraint(int Partition_Parameter) {
  if (Partition_Parameter == 2) {
    SMTCell::writeConstraint(";Set Partition Constraints\n");
    // # Lower Group => Right Side
    for (int i = 0; i < SMTCell::getPInstPartitionCnt() - 1; i++) {
      // PMOS
      int j = i + 1;
      for (int k = 0; k < SMTCell::getPInstPartitionInstIndicesCnt(i); k++) {
        for (int l = 0; l < SMTCell::getPInstPartitionInstIndicesCnt(j); l++) {
          SMTCell::writeConstraint(
              fmt::format("(assert (bvsgt x{} x{}))\n",
                          SMTCell::getPInstPartitionInstIdx(i, k),
                          SMTCell::getPInstPartitionInstIdx(j, l)));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    // # Upper Group => Left Side
    for (int i = 0; i < SMTCell::getNInstPartitionCnt() - 1; i++) {
      // NMOS
      int j = i + 1;
      for (int k = 0; k < SMTCell::getNInstPartitionInstIndicesCnt(i); k++) {
        for (int l = 0; l < SMTCell::getNInstPartitionInstIndicesCnt(j); l++) {
          SMTCell::writeConstraint(
              fmt::format("(assert (bvsgt x{} x{}))\n",
                          SMTCell::getNInstPartitionInstIdx(i, k),
                          SMTCell::getNInstPartitionInstIdx(j, l)));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }
    SMTCell::writeConstraint(";End of Partition Constraints\n");
  }

  if (Partition_Parameter == 1) {
    SMTCell::writeConstraint(";Set Relative Condition for Transistors whose "
                             "Gate Pins should be in the same column\n");
    std::vector<int> arr_out_p;
    std::vector<int> arr_in_p;
    std::vector<int> arr_out_n;
    std::vector<int> arr_in_n;
    std::map<int, int> h_outins;
    std::map<int, int> h_totins;

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
          if (h_outins.find(source_inst_idx) == h_outins.end()) {
            if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_out_p.push_back(source_inst_idx);
              fmt::print("Output Instance PMOS x{}\n", source_inst_idx);
            } else {
              arr_out_n.push_back(source_inst_idx);
              fmt::print("Output Instance NMOS x{}\n", source_inst_idx);
            }
            h_outins[source_inst_idx] = 1;
          }
        }
      }

      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
            if (h_outins.find(sink_inst_idx) == h_outins.end()) {
              if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
                arr_out_p.push_back(sink_inst_idx);
                fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
              } else {
                arr_out_n.push_back(sink_inst_idx);
                fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
              }
              h_outins[sink_inst_idx] = 1;
            }
          }
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (h_outins.find(source_inst_idx) == h_outins.end() &&
            h_totins.find(source_inst_idx) == h_totins.end()) {
          if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
            arr_in_p.push_back(source_inst_idx);
            fmt::print("Input Instance PMOS x{}\n", source_inst_idx);
          } else {
            arr_in_n.push_back(source_inst_idx);
            fmt::print("Input Instance NMOS x{}\n", source_inst_idx);
          }
          h_totins[source_inst_idx] = 1;
        }
      }
      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (h_outins.find(sink_inst_idx) == h_outins.end() &&
              h_totins.find(sink_inst_idx) == h_totins.end()) {
            if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_in_p.push_back(sink_inst_idx);
              fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
            } else {
              arr_in_n.push_back(sink_inst_idx);
              fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
            }
            h_totins[sink_inst_idx] = 1;
          }
        }
      }
    }

    int numOutP = arr_out_p.size();
    int numOutN = arr_out_n.size();
    int numInP = arr_in_p.size();
    int numInN = arr_in_n.size();

    if (numOutP > 0 && numInP > 0) {
      for (int i = 0; i < numOutP; i++) {
        for (int j = 0; j < numInP; j++) {
          SMTCell::writeConstraint(fmt::format("(assert (bvsgt x{} x{}))\n",
                                               arr_out_p[i], arr_in_p[j]));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    if (numOutN > 0 && numInN > 0) {
      for (int i = 0; i < numOutN; i++) {
        for (int j = 0; j < numInN; j++) {
          SMTCell::writeConstraint(fmt::format("(assert (bvsgt x{} x{}))\n",
                                               arr_out_n[i], arr_in_n[j]));
          SMTCell::cnt("l", 0);
          SMTCell::cnt("l", 0);
          SMTCell::cnt("c", 0);
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      std::vector<std::pair<int, int>> arr_sink;
      std::map<int, int> h_instidx;
      std::map<int, int> h_instpair;
      std::string tmp_str = "";
      int cnt_pair = 0;

      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());

      int width_source = tmp_finger_source[0] * 2 + 1;

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // ## Sink MaxFlow Indicator
        if (SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex) ==
            SMTCell::getKeySON()) {
          continue;
        }

        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        // ## Skip If Source/Sink TR is in the same region
        if (source_inst_idx <= SMTCell::getLastIdxPMOS() &&
            sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
          continue;
        }

        if (source_inst_idx > SMTCell::getLastIdxPMOS() &&
            sink_inst_idx > SMTCell::getLastIdxPMOS()) {
          continue;
        }

        // ## Skip if Source/Sink Pin is not "Gate" Pin
        if (source_pin->getPinType() != "G" && sink_pin->getPinType() != "G") {
          continue;
        }

        // ## Skip if Source/Sink Pin are the same
        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
          arr_sink.push_back(std::make_pair(sink_inst_idx, width_sink));
          h_instidx[sink_inst_idx] = 1;
        }
      }

      std::vector<std::pair<int, int>> arr_p;
      std::vector<std::pair<int, int>> arr_n;
      h_instidx.clear();

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        // ## Sink MaxFlow Indicator
        if (SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex) ==
            SMTCell::getKeySON()) {
          continue;
        }

        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (sink_pin->getPinType() == "G") {
          if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
            // PMOS
            if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
              arr_p.push_back(std::make_pair(sink_inst_idx, width_sink));
              h_instidx[sink_inst_idx] = 1;
            }
          } else {
            // NMOS
            if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
              arr_n.push_back(std::make_pair(sink_inst_idx, width_sink));
              h_instidx[sink_inst_idx] = 1;
            }
          }
        }
      }

      int numP = arr_p.size();
      int numN = arr_n.size();
      int numS = arr_sink.size();

      if (numS > 0 && h_outins.find(source_inst_idx) == h_outins.end()) {
        SMTCell::writeConstraint("(assert (or");

        for (int i = 0; i < numS; i++) {
          int len = SMTCell::getBitLengthNumTrackV();
          fmt::print("Gate to Gate : Inst/Width[{}/{}] [{}/{}]\n",
                     source_inst_idx, width_source, arr_sink[i].first,
                     arr_sink[i].second);
          if (width_source == arr_sink[i].second) {
            SMTCell::writeConstraint(
                fmt::format(" (= x{} {})", source_inst_idx, arr_sink[i].first));

            if (width_source > 3) {
              for (int k = 0; k = ((width_source - 1) / 2 - 1); k++) {
                SMTCell::writeConstraint(fmt::format(
                    " (= x{} (bvadd x{} (_ bv{} {})))", source_inst_idx,
                    arr_sink[i].first,
                    (2 * (k + 1)) * SMTCell::getMetalOneStep(), len));

                SMTCell::writeConstraint(fmt::format(
                    " (= x{} (bvadd x{} (_ bv{} {})))", arr_sink[i].first,
                    source_inst_idx, (2 * (k + 1)) * SMTCell::getMetalOneStep(),
                    len));
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
                SMTCell::cnt("l", 0);
              }
            }

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          } else if (width_source > arr_sink[i].second) {
            SMTCell::writeConstraint(
                fmt::format(" (= x{} {})", source_inst_idx, arr_sink[i].first));
            SMTCell::writeConstraint(
                fmt::format(" (= x{} (bvadd x{} (_ bv{} {})))",
                            arr_sink[i].first, source_inst_idx,
                            (width_source - arr_sink[i].second) *
                                SMTCell::getMetalOneStep(),
                            len));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          } else {
            SMTCell::writeConstraint(
                fmt::format(" (= x{} {})", source_inst_idx, arr_sink[i].first));
            SMTCell::writeConstraint(
                fmt::format(" (= x{} (bvadd x{} (_ bv{} {})))", source_inst_idx,
                            arr_sink[i].first,
                            (arr_sink[i].second - width_source) *
                                SMTCell::getMetalOneStep(),
                            len));
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);

            if (h_instpair.find(source_inst_idx) == h_instpair.end()) {
              cnt_pair++;
              h_instpair[source_inst_idx] = 1;
            }
          }
        }
        SMTCell::writeConstraint("))\n");
        SMTCell::cnt("c", 0);
      }
    }

    SMTCell::writeConstraint(
        ";set relative position constraints for transistors which share the "
        "same net information\n");

    int def_offset =
        int((SMTCell::getRealNumTrackV() / SMTCell::getMetalOneStep()) / 1.7);

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      std::vector<std::pair<int, int>> arr_inst;
      std::map<int, int> h_instidx;
      std::map<int, int> h_instpair;
      int cnt_pair = 0;
      int width_p = 0;
      int width_n = 0;
      int isExtNet = 0;

      // ## Source MaxFlow Indicator
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      std::vector<int> tmp_finger_source = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(source_inst_idx)->getInstWidth(),
          SMTCell::getTrackEachPRow());
      int width_source = tmp_finger_source[0] * 2 + 1;

      if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
        if (h_instidx.find(source_inst_idx) == h_instidx.end()) {
          arr_inst.push_back(std::make_pair(source_inst_idx, width_source));
          h_instidx[source_inst_idx] = 1;
          width_p += width_source;
        }
      } else {
        if (h_instidx.find(source_inst_idx) == h_instidx.end()) {
          arr_inst.push_back(std::make_pair(source_inst_idx, width_source));
          h_instidx[source_inst_idx] = 1;
          width_n += width_source;
        }
      }

      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {

        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);

        std::vector<int> tmp_finger_sink = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(sink_inst_idx)->getInstWidth(),
            SMTCell::getTrackEachPRow());
        int width_sink = tmp_finger_sink[0] * 2 + 1;

        if (source_inst_idx == sink_inst_idx) {
          continue;
        }

        if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
          if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
            arr_inst.push_back(std::make_pair(sink_inst_idx, width_sink));
            h_instidx[sink_inst_idx] = 1;
            width_p += width_sink;
          }
        } else {
          if (h_instidx.find(sink_inst_idx) == h_instidx.end()) {
            arr_inst.push_back(std::make_pair(sink_inst_idx, width_sink));
            h_instidx[sink_inst_idx] = 1;
            width_n += width_sink;
          }
        }
      }

      int numInst = arr_inst.size();
      int pos_offset = 0;
      if (width_p > width_n && width_p > def_offset) {
        pos_offset = width_p;
      } else if (width_n > width_p && width_n > def_offset) {
        pos_offset = width_n;
      } else {
        pos_offset = def_offset;
      }

      if (isExtNet == 1 && numInst > 0) {
        for (int i = 0; i < numInst; i++) {
          for (int j = i + 1; j < numInst; j++) {
            int len = SMTCell::getBitLengthNumTrackV();
            fmt::print("Relative Position : Inst/Width[{}/{}][{}/{}]\n",
                       arr_inst[i].first, arr_inst[i].second, arr_inst[j].first,
                       arr_inst[j].second);

            SMTCell::writeConstraint(" (assert (or ");
            if ((arr_inst[i].first <= SMTCell::getLastIdxPMOS() &&
                 arr_inst[j].first > SMTCell::getLastIdxPMOS()) ||
                (arr_inst[i].first > SMTCell::getLastIdxPMOS() &&
                 arr_inst[j].first <= SMTCell::getLastIdxPMOS())) {
              SMTCell::writeConstraint(fmt::format(
                  " (= x{} x{})", arr_inst[i].first, arr_inst[j].first));
            }

            SMTCell::writeConstraint(fmt::format(
                " (and (bvsgt x{} x{}) (bvsle x{} (bvadd x{} (_ bv{} {}))))",
                arr_inst[i].first, arr_inst[j].first, arr_inst[i].first,
                arr_inst[j].first, pos_offset * SMTCell::getMetalOneStep(),
                len));
            SMTCell::writeConstraint(fmt::format(
                " (and (bvslt x{} x{}) (bvsle x{} (bvadd x{} (_ bv{} {}))))",
                arr_inst[i].first, arr_inst[j].first, arr_inst[j].first,
                arr_inst[i].first, pos_offset * SMTCell::getMetalOneStep(),
                len));
            SMTCell::writeConstraint("))\n");
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("l", 0);
            SMTCell::cnt("c", 0);
          }
        }
      }
    }
  }
}

/**
 * Write Cost function for FETs
 * 
 * @param   Partition_Parameter   whether to enable partition constraints
 *
 * @return  void
 */
void Placement::write_cost_func_mos(FILE *fp) {
  fmt::print(fp, "(assert (bvsle COST_SIZE_P (_ bv{} {})))\n",
             SMTCell::getRealNumTrackV(), SMTCell::getBitLengthNumTrackV());
  fmt::print(fp, "(assert (bvsle COST_SIZE_N (_ bv{} {})))\n",
             SMTCell::getRealNumTrackV(), SMTCell::getBitLengthNumTrackV());
}

/**
 * Write Cost function for FETs based on partition
 * 
 * @param   *fp   file pointer
 * @param   Partition_Parameter   whether to enable partition constraints
 *
 * @return  void
 */
void Placement::write_cost_func(FILE *fp, int Partition_Parameter) {
  int isPRT_P = 0;
  int isPRT_N = 0;
  if (Partition_Parameter == 2) {
    // PMOS
    int numP = SMTCell::getPInstPartitionCnt();

    if (numP > 0) {
      int numInstP = SMTCell::getPInstPartitionInstIndicesCnt(0);
      fmt::print("Group {} NumInst {}\n", SMTCell::getPInstPartitionGroupIdx(0),
                 numInstP);

      fmt::print(fp, "(assert (= COST_SIZE_P");
      for (int j = 0; j <= numInstP - 2; j++) {
        fmt::print(fp, " (max");
      }
      int i = SMTCell::getPInstPartitionInstIdx(0, 0);

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);

      fmt::print(fp, " (bvadd x{} {})", i, s_first);

      for (int j = 1; j <= numInstP - 1; j++) {
        i = SMTCell::getPInstPartitionInstIdx(0, j);
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }

      fmt::print(fp, "))\n");
      isPRT_P = 1;
    }

    // NMOS
    int numN = SMTCell::getNInstPartitionCnt();

    if (numN > 0) {
      int numInstN = SMTCell::getNInstPartitionInstIndicesCnt(0);
      fmt::print("Group {} NumInst {}\n", SMTCell::getNInstPartitionGroupIdx(0),
                 numInstN);

      // numN = arr_bound.size();

      // if (numN > 0) {
      fmt::print(fp, "(assert (= COST_SIZE_N");
      for (int j = 0; j <= numInstN - 2; j++) {
        fmt::print(fp, " (max");
      }
      // int i = arr_bound[0];
      int i = SMTCell::getNInstPartitionInstIdx(0, 0);
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);

      fmt::print(fp, " (bvadd x{} {})", i, s_first);

      for (int j = 1; j <= numInstN - 1; j++) {
        // i = arr_bound[j];
        i = SMTCell::getNInstPartitionInstIdx(0, j);
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger = (bmp::msb(2 * tmp_finger[0] + 1) + 1);
        s_first = fmt::format("(_ bv{} {})", 2 * tmp_finger[0], len);
        fmt::print(fp, " (bvadd x{} {}))", i, s_first);
      }

      fmt::print(fp, "))\n");
      isPRT_N = 1;
    }
  } else if (Partition_Parameter == 1) {
    std::vector<int> arr_out_p;
    std::vector<int> arr_in_p;
    std::vector<int> arr_out_n;
    std::vector<int> arr_in_n;
    std::map<int, int> h_outins;
    std::map<int, int> h_totins;

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
          if (h_outins.find(source_inst_idx) == h_outins.end()) {
            if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_out_p.push_back(source_inst_idx);
              fmt::print("Output Instance PMOS x{}\n", source_inst_idx);
            } else {
              arr_out_n.push_back(source_inst_idx);
              fmt::print("Output Instance NMOS x{}\n", source_inst_idx);
            }
            h_outins[source_inst_idx] = 1;
          }
        }
      }

      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (SMTCell::ifOutNet(SMTCell::getNet(netIndex)->getNetID())) {
            if (h_outins.find(sink_inst_idx) == h_outins.end()) {
              if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
                arr_out_p.push_back(sink_inst_idx);
                fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
              } else {
                arr_out_n.push_back(sink_inst_idx);
                fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
              }
              h_outins[sink_inst_idx] = 1;
            }
          }
        }
      }
    }

    for (int netIndex = 0; netIndex < SMTCell::getNetCnt(); netIndex++) {
      // ## Source
      std::string pidx_s = SMTCell::getNet(netIndex)->getSource_ofNet();
      Pin *source_pin = SMTCell::getPin(pidx_s);
      int source_inst_idx = SMTCell::getPinInstIdx(source_pin);
      // Drain pin or Source pin
      if (source_pin->getPinType() != "G") {
        if (h_outins.find(source_inst_idx) == h_outins.end() &&
            h_totins.find(source_inst_idx) == h_totins.end()) {
          if (source_inst_idx <= SMTCell::getLastIdxPMOS()) {
            arr_in_p.push_back(source_inst_idx);
            fmt::print("Input Instance PMOS x{}\n", source_inst_idx);
          } else {
            arr_in_n.push_back(source_inst_idx);
            fmt::print("Input Instance NMOS x{}\n", source_inst_idx);
          }
          h_totins[source_inst_idx] = 1;
        }
      }
      // ## Sink
      for (int commodityIndex = 0;
           commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
           commodityIndex++) {
        std::string pidx_t =
            SMTCell::getNet(netIndex)->getSinks_inNet(commodityIndex);
        Pin *sink_pin = SMTCell::getPin(pidx_t);
        int sink_inst_idx = SMTCell::getPinInstIdx(sink_pin);
        // Drain pin or Source pin
        if (sink_pin->getPinType() != "G") {
          if (h_outins.find(sink_inst_idx) == h_outins.end() &&
              h_totins.find(sink_inst_idx) == h_totins.end()) {
            if (sink_inst_idx <= SMTCell::getLastIdxPMOS()) {
              arr_in_p.push_back(sink_inst_idx);
              fmt::print("Input Instance PMOS x{}\n", sink_inst_idx);
            } else {
              arr_in_n.push_back(sink_inst_idx);
              fmt::print("Input Instance NMOS x{}\n", sink_inst_idx);
            }
            h_totins[sink_inst_idx] = 1;
          }
        }
      }
    }

    int numOutP = arr_out_p.size();
    int numOutN = arr_out_n.size();
    int numInP = arr_in_p.size();
    int numInN = arr_in_n.size();

    if (numOutP > 1) {
      fmt::print(fp, "(assert (= COST_SIZE_P");
      for (int j = 0; j <= numOutP - 2; j++) {
        fmt::print(fp, " (max");
      }
      int i = arr_out_p[0];

      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);

      fmt::print(fp, " (bvadd x{} {}", i, s_first);

      for (int j = 1; j <= numOutP - 1; j++) {
        i = arr_out_p[j];
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, "))\n");
      isPRT_P = 1;
    } else if (numOutP == 1) {
      fmt::print(fp, "(assert (= COST_SIZE_P");
      for (int j = 0; j <= numOutP - 1; j++) {
        int i = arr_out_p[j];
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        int len = SMTCell::getBitLengthNumTrackV();
        int len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        std::string s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, ")\n");
      isPRT_P = 1;
    }

    if (numOutN > 1) {
      fmt::print(fp, "(assert (= COST_SIZE_N");
      for (int j = 0; j <= numOutN - 2; j++) {
        fmt::print(fp, " (max");
      }
      int i = arr_out_n[0];
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
      fmt::print(fp, " (bvadd x{} {}", i, s_first);

      for (int j = 1; j <= numOutN - 1; j++) {
        i = arr_out_n[j];
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, "))\n");
      isPRT_N = 1;
    } else if (numOutN == 1) {
      fmt::print(fp, "(assert (= COST_SIZE_N");
      for (int j = 0; j <= numOutN - 1; j++) {
        int i = arr_out_n[j];
        std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        int len = SMTCell::getBitLengthNumTrackV();
        int len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        std::string s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, ")\n");
      isPRT_N = 1;
    }

    if (isPRT_P == 0) {
      fmt::print(fp, "(assert (= COST_SIZE_P");
      for (int j = 0; j <= SMTCell::getLastIdxPMOS(); j++) {
        fmt::print(fp, " (max");
      }
      int i = 0;
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      // never used, ignored
      // std::string tmp_str;
      // if (len > 1) {
      //   for (int i = 0; i <= len - len_finger - 1; i++) {
      //     tmp_str += "0";
      //   }
      // }

      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);

      fmt::print(fp, " (bvadd x{} {}", i, s_first);
      for (int j = 1; j <= SMTCell::getLastIdxPMOS(); j++) {
        i = j;
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        // never used, ignored
        // std::string tmp_str;
        // if (len > 1) {
        //   for (int i = 0; i <= len - len_finger - 1; i++) {
        //     tmp_str += "0";
        //   }
        // }
        s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, "))\n");
    }

    if (isPRT_N == 0) {
      fmt::print(fp, "(assert (= COST_SIZE_N");
      for (int j = SMTCell::getLastIdxPMOS() + 1;
           j <= SMTCell::getNumInstance() - 2; j++) {
        fmt::print(fp, " (max");
      }
      int i = SMTCell::getLastIdxPMOS() + 1;
      std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      int len = SMTCell::getBitLengthNumTrackV();
      int len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();

      std::string s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);

      fmt::print(fp, " (bvadd x{} {}", i, s_first);
      for (int j = SMTCell::getLastIdxPMOS() + 2;
           j <= SMTCell::getNumInstance() - 1; j++) {
        i = j;
        tmp_finger = SMTCell::getAvailableNumFinger(
            SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
        len_finger =
            (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
        s_first = fmt::format(
            "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
        fmt::print(fp, " (bvadd x{} {}", i, s_first);
      }
      fmt::print(fp, "))\n");
    }
  } else {
    // fmt::print("HERE\n");
    // PMOS
    fmt::print(fp, "(assert (= COST_SIZE_P");
    for (int j = 0; j <= SMTCell::getLastIdxPMOS() - 1; j++) {
      fmt::print(fp, " (max");
    }
    int i = 0;
    std::vector<int> tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    int len = SMTCell::getBitLengthNumTrackV();
    int len_finger =
        (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
    std::string tmp_str;

    if (len > 1) {
      for (int i = 0; i < len - len_finger - 1; i++) {
        tmp_str += "0";
      }
    }

    std::string s_first = fmt::format(
        "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
    fmt::print(fp, " (bvadd x{} {})", i, s_first);

    for (int j = 1; j <= SMTCell::getLastIdxPMOS(); j++) {
      i = j;
      tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string tmp_str;

      if (len > 1) {
        for (int i = 0; i < len - len_finger - 1; i++) {
          tmp_str += "0";
        }
      }

      s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
      fmt::print(fp, " (bvadd x{} {}))", i, s_first);
    }
    fmt::print(fp, "))\n");

    // NMOS
    fmt::print(fp, "(assert (= COST_SIZE_N");
    for (int j = SMTCell::getLastIdxPMOS() + 1;
         j <= SMTCell::getNumInstance() - 2; j++) {
      fmt::print(fp, " (max");
    }

    i = SMTCell::getLastIdxPMOS() + 1;
    tmp_finger = SMTCell::getAvailableNumFinger(
        SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
    len = SMTCell::getBitLengthNumTrackV();
    len_finger =
        (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
    tmp_str.clear();

    if (len > 1) {
      for (int i = 0; i < len - len_finger - 1; i++) {
        tmp_str += "0";
      }
    }

    s_first = fmt::format("(_ bv{} {})",
                          2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
    fmt::print(fp, " (bvadd x{} {})", i, s_first);

    for (int j = SMTCell::getLastIdxPMOS() + 2;
         j <= SMTCell::getNumInstance() - 1; j++) {
      i = j;
      tmp_finger = SMTCell::getAvailableNumFinger(
          SMTCell::getInst(i)->getInstWidth(), SMTCell::getTrackEachPRow());
      len_finger =
          (bmp::msb(2 * tmp_finger[0] + 1) + 1) * SMTCell::getMetalOneStep();
      std::string tmp_str;

      if (len > 1) {
        for (int i = 0; i < len - len_finger - 1; i++) {
          tmp_str += "0";
        }
      }

      s_first = fmt::format(
          "(_ bv{} {})", 2 * tmp_finger[0] * SMTCell::getMetalOneStep(), len);
      fmt::print(fp, " (bvadd x{} {}))", i, s_first);
    }
    fmt::print(fp, "))\n");
  }
}

/**
 * Associate Top Track Usage
 * 
 * @param   *fp   file pointer
 *
 * @return  void
 */
void Placement::write_top_metal_track_usage(FILE *fp) {
  // top metal track usage
  for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
    fmt::print(fp, "(assert (= M2_TRACK_{} (or", row);
    for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
         udEdgeIndex++) {
      int step = 0;
      for (int col = 0; col < SMTCell::getRealNumTrackV();
           col += SMTCell::getMetalOneStep()) {
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
        int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
        int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
        int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
        int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;

        if (fromMetal == 1 || toMetal == 1) {
          step = SMTCell::getMetalOneStep();
        } else {
          step = SMTCell::getMetalThreeStep();
        }

        if (fromMetal == 3 && toMetal == 4 &&
            (fromRow == row && toRow == row) &&
            (fromCol == col && toCol == col)) {
          std::string variable_name = fmt::format(
              "M_{}_{}",
              SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
              SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
          if (SMTCell::ifVar(variable_name)) {
            fmt::print(fp, " {}", variable_name);
          }
        }
      }
    }

    fmt::print(fp, ")))\n");
  }

  for (auto en : SMTCell::getExtNet()) {
    int netIndex = SMTCell::getNetIdx(std::to_string(en.first));
    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      fmt::print(fp, "(assert (= N{}_M2_TRACK_{} (or", en.first, row);
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;

        int step = 0;

        if (fromMetal == 1 || toMetal == 1) {
          step = SMTCell::getMetalOneStep();
        } else {
          step = SMTCell::getMetalThreeStep();
        }

        for (int col = 0; col < SMTCell::getRealNumTrackV(); col += step) {
          int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
          int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
          int fromRow = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->row_;
          int toRow = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->row_;
          if (fromMetal == 3 && toMetal == 4 &&
              (fromRow == row && toRow == row) &&
              (fromCol == col && toCol == col)) {
            // fmt::print("FLAG3\n");
            for (int commodityIndex = 0;
                 commodityIndex < SMTCell::getNet(netIndex)->getNumSinks();
                 commodityIndex++) {
              // fmt::print("FLAG4\n");
              std::string variable_name =
                  fmt::format("N{}_C{}_E_{}_{}", en.first, commodityIndex,
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdFromEdge()
                                  ->getVname(),
                              SMTCell::getUdEdge(udEdgeIndex)
                                  ->getUdToEdge()
                                  ->getVname());
              // fmt::print("{}\n", variable_name);
              if (SMTCell::ifVar(variable_name)) {
                // fmt::print("FLAG5\n");
                fmt::print(fp, " {}", variable_name);
              }
            }
          }
        }
      }
      fmt::print(fp, ")))\n");
    }
    fmt::print(fp, "(assert (= N{}_M2_TRACK (or", en.first);
    for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
      fmt::print(fp, " N{}_M2_TRACK_{}", en.first, row);
    }
    fmt::print(fp, ")))\n");
  }
}

/**
 * Minimize all cost function
 * 
 * @param   *fp   file pointer
 * @param   Partition_Parameter   whether to enable partition constraints
 *
 * @return  void
 */
void Placement::write_minimize_cost_func(FILE *fp, int Partition_Parameter) {
  int idx_obj = 0;
  int limit_obj = 150;

  if (SMTCell::getNumMetalLayer() == 4) {
    limit_obj = 150;
  } else {
    limit_obj = 50;
  }

  int num_netOpt = SMTCell::getNetOptCnt();
  if (Partition_Parameter == 2 && num_netOpt > 0) {
    std::string str_opt;
    str_opt = "(minimize (bvadd";
    idx_obj = 0;
    // set it already, no need to set it again
    // if (SMTCell::getNumTrack() == 4) {
    //   limit_obj = 150;
    // } else {
    //   limit_obj = 50;
    // }
    fmt::print(fp, str_opt);

    int step = SMTCell::getGCDStep();
    for (int col = 0; col < SMTCell::getRealNumTrackV(); col += step) {
      if (idx_obj >= limit_obj) {
        idx_obj = 0;
        fmt::print(fp, "))\n");
        fmt::print(fp, "(minimize (bvadd");
      }
      for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
           udEdgeIndex++) {
        int fromMetal =
            SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
        int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
        int fromCol = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->col_;
        int toCol = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->col_;
        if (fromMetal == toMetal && toMetal == 4) {
          // same as foreach my $key(keys %h_net_opt)
          for (int i = 0; i < num_netOpt; i++) {
            std::string variable_name =
                fmt::format("E_{}_{}",
                            SMTCell::getUdEdge(udEdgeIndex)
                                ->getUdFromEdge()
                                ->getVname(),
                            SMTCell::getUdEdge(udEdgeIndex)
                                ->getUdToEdge()
                                ->getVname());
            if (SMTCell::ifVar(variable_name)) {
              fmt::print(fp, " (ite (= {} true) (_ bv{} 32) (_ bv0 32))",
                         variable_name,
                         SMTCell::getUdEdge(udEdgeIndex)->getMCost());
              idx_obj++;
            }
          }
        }
      }
    }
    fmt::print(fp, "))\n");
    idx_obj = 0;
  }

  idx_obj = 0;
  limit_obj = 10;
  fmt::print(fp, "(minimize (bvadd");
  for (int row = 0; row <= SMTCell::getNumTrackH() - 3; row++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "))\n");
      fmt::print(fp, "(minimize (bvadd");
    }
    fmt::print(fp, " (ite (= M2_TRACK_{} true) (_ bv1 {}) (_ bv0 {}))", row,
               SMTCell::getBitLengthNumTrackH(),
               SMTCell::getBitLengthNumTrackH());
    idx_obj++;
  }
  fmt::print(fp, "))\n");

  idx_obj = 0;
  if (SMTCell::getNumTrack() == 4) {
    limit_obj = 150;
  } else {
    limit_obj = 50;
  }

  std::string tmp_str_obj;
  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
    if (toMetal == 4) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} 32) (_ bv0 32))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost());
        idx_obj++;
      }
    }
  }

  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  idx_obj = 0;
  tmp_str_obj.clear();

  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
    if (fromMetal != toMetal && (toMetal >= 2 && toMetal <= 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} 32) (_ bv0 32))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost());
        idx_obj++;
      }
    }
  }

  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  idx_obj = 0;
  tmp_str_obj.clear();

  for (int udEdgeIndex = 0; udEdgeIndex < SMTCell::getUdEdgeCnt();
       udEdgeIndex++) {
    if (idx_obj >= limit_obj) {
      idx_obj = 0;
      fmt::print(fp, "(minimize (bvadd");
      fmt::print(fp, tmp_str_obj.c_str());
      fmt::print(fp, "))\n");
      tmp_str_obj.clear();
    }
    int fromMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->metal_;
    int toMetal = SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->metal_;
    if (fromMetal == toMetal && (toMetal >= 2 && toMetal <= 3)) {
      std::string variable_name = fmt::format(
          "M_{}_{}",
          SMTCell::getUdEdge(udEdgeIndex)->getUdFromEdge()->getVname(),
          SMTCell::getUdEdge(udEdgeIndex)->getUdToEdge()->getVname());
      if (SMTCell::ifVar(variable_name)) {
        tmp_str_obj += fmt::format(" (ite (= {} true) (_ bv{} 32) (_ bv0 32))",
                                   variable_name,
                                   SMTCell::getUdEdge(udEdgeIndex)->getMCost());
        idx_obj++;
      }
    }
  }

  if (tmp_str_obj.size() > 0) {
    fmt::print(fp, "(minimize (bvadd");
    fmt::print(fp, tmp_str_obj.c_str());
    fmt::print(fp, "))\n");
  }

  idx_obj = 0;
  tmp_str_obj.clear();

  // Ignored the case $MM_Parameter < 4 because it never happens in our
  // formulation
}