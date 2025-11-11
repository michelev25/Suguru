# suguru_niveis_bt_SUMARY2_multi.py
# Python 3.x + tkinter
# Estratégia por nível: CHUTE (MRV, 1 valor) -> aplica regras determinísticas até travar.
# Destaques (mantidos):
# - Pencil marks (candidatos)
# - MRV em amarelo antes do chute
# - Badges "B{k}" para chutes confirmados (persistentes após redraw)
# - Rollback visual imediato (removendo badge do nível desfeito)
# - Checagens de restrição (regiões e vizinhos)
# - Painel de histórico (contradições/rollback/commits/deduções)
# - Contador de determinísticas EXATO (decrementa no rollback)
# - Auto-run: aplica REGRAS primeiro; se travar, faz 1 NÍVEL (BT + Regras)
# - ***ATUALIZAÇÕES***:
#   * Removido resumo final que redimensionava e repetia estatísticas
#   * Persistência correta dos badges de backtracking
#   * Autorun ajustado para "regras primeiro"
#   * SUPORTE A MÚLTIPLOS TAMANHOS (6x6, 8x8, 12x10, 15x10, 15x10 n=6)
#   * Seletor de arquivo de instâncias + redimensionamento automático do tabuleiro
#   * Pencil marks até 6 candidatos (p/ variantes com regiões de tamanho 6)

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import itertools
import os
import re
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple

# =========================
# Parsing do arquivo
# =========================

def decode_givens(code: str, width: int, height: int):
    out = []
    for ch in code.strip():
        if ch.isalpha():
            blanks = ord(ch.lower()) - ord('a') + 1
            out.extend([None] * blanks)
        elif ch.isdigit():
            out.append(int(ch))
    expected = width * height
    if len(out) != expected:
        out = (out + [None]*expected)[:expected]
    return out

def parse_answer(ans: str, width: int, height: int):
    digits = [int(ch) for ch in ans.strip() if ch.isdigit()]
    expected = width * height
    if len(digits) != expected:
        digits = (digits + [0]*expected)[:expected]
    return digits

def load_puzzles(path: str):
    puzzles = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 6:
                parts = line.strip().split()
                if len(parts) < 6:
                    continue
                name, w, h, giv, layout, ans = parts[:6]
                comment = " ".join(parts[6:]) if len(parts) > 6 else ""
            else:
                name, w, h, giv, layout, ans = parts[:6]
                comment = parts[6] if len(parts) > 6 else ""
            width = int(w); height = int(h)
            givens = decode_givens(giv, width, height)
            answer = parse_answer(ans, width, height)
            puzzles.append({
                "name": name, "width": width, "height": height,
                "givens": givens, "layout": layout, "answer": answer, "comment": comment
            })
    return puzzles

# =========================
# Helpers
# =========================

def rc2i(r, c, w): return r * w + c
def i2rc(i, w): return divmod(i, w)

# =========================
# Deterministic Solver
# =========================

class DeterministicSolver:
    def __init__(self, width, height, layout, initial):
        self.w = width
        self.h = height
        self.N = self.w * self.h
        self.layout = layout
        self.board = initial[:]
        self.regions = {}
        for i, ch in enumerate(layout):
            self.regions.setdefault(ch, []).append(i)
        self.neigh = {}
        for i in range(self.N):
            r, c = i2rc(i, self.w)
            ns = []
            for dr in (-1,0,1):
                for dc in (-1,0,1):
                    if dr==0 and dc==0: continue
                    rr, cc = r+dr, c+dc
                    if 0<=rr<self.h and 0<=cc<self.w:
                        ns.append(rc2i(rr,cc,self.w))
            self.neigh[i] = ns
        self.cands = [set() for _ in range(self.N)]
        self._init_candidates()

    def _init_candidates(self):
        for i in range(self.N):
            ch = self.layout[i]
            n = len(self.regions[ch])
            if self.board[i] is not None:
                self.cands[i] = {self.board[i]}
            else:
                poss = set(range(1, n+1))
                for j in self.regions[ch]:
                    v = self.board[j]
                    if v is not None: poss.discard(v)
                for nbh in self.neigh[i]:
                    v = self.board[nbh]
                    if v is not None: poss.discard(v)
                self.cands[i] = poss

    def _elim(self, i, v):
        if v in self.cands[i] and len(self.cands[i])>1:
            self.cands[i].remove(v)
            return True
        return False

    def _propagate_singleton(self, i):
        v = next(iter(self.cands[i]))
        for j in self.regions[self.layout[i]]:
            if j!=i: self._elim(j, v)
        for n in self.neigh[i]:
            self._elim(n, v)

    def _assign_from_singletons(self):
        changed=False
        for i in range(self.N):
            if len(self.cands[i])==1 and self.board[i] is None:
                self.board[i] = next(iter(self.cands[i]))
                changed=True
        return changed

    def _hidden_single(self):
        changed=False
        for ch,cells in self.regions.items():
            n = len(cells)
            for d in range(1,n+1):
                occ=[i for i in cells if d in self.cands[i]]
                if len(occ)==1:
                    i=occ[0]
                    if len(self.cands[i])>1:
                        self.cands[i]={d}
                        if self.board[i] is None:
                            self.board[i]=d
                        changed=True
        return changed

    def _naked_pairs(self):
        changed=False
        for ch,cells in self.regions.items():
            pairs={}
            for i in cells:
                if len(self.cands[i])==2:
                    key=tuple(sorted(self.cands[i]))
                    pairs.setdefault(key,[]).append(i)
            for key,idxs in pairs.items():
                if len(idxs)==2:
                    digits=set(key)
                    for j in cells:
                        if j not in idxs:
                            for d in digits:
                                if self._elim(j,d):
                                    changed=True
        return changed

    def _hidden_pairs(self):
        changed=False
        for ch,cells in self.regions.items():
            n=len(cells)
            occ={d:[i for i in cells if d in self.cands[i]] for d in range(1,n+1)}
            for d1,d2 in itertools.combinations(range(1,n+1),2):
                s=set(occ[d1])|set(occ[d2])
                if len(s)==2:
                    for i in s:
                        newset=self.cands[i]&{d1,d2}
                        if newset!=self.cands[i]:
                            self.cands[i]=set(newset)
                            changed=True
        return changed

    def _naked_triples(self):
        changed=False
        for ch,cells in self.regions.items():
            for triple in itertools.combinations(cells,3):
                union=set().union(*(self.cands[i] for i in triple))
                if 1<len(union)==3:
                    for j in cells:
                        if j not in triple:
                            for d in union:
                                if self._elim(j,d):
                                    changed=True
        return changed

    def _hidden_triples(self):
        changed=False
        for ch,cells in self.regions.items():
            n=len(cells)
            occ={d:[i for i in cells if d in self.cands[i]] for d in range(1,n+1)}
            for trio in itertools.combinations(range(1,n+1),3):
                occ_union=set().union(*(set(occ[d]) for d in trio))
                if len(occ_union)==3:
                    for i in occ_union:
                        newset=self.cands[i]&set(trio)
                        if newset!=self.cands[i]:
                            self.cands[i]=set(newset)
                            changed=True
        return changed

    def solve(self):
        changed=True
        while changed:
            changed=False
            if self._assign_from_singletons(): changed=True
            for i in range(self.N):
                if len(self.cands[i])==1:
                    self._propagate_singleton(i)

            if self._hidden_single(): changed=True
            if self._assign_from_singletons(): changed=True
            for i in range(self.N):
                if len(self.cands[i])==1:
                    self._propagate_singleton(i)

            if self._naked_pairs(): changed=True
            if self._hidden_pairs(): changed=True
            if self._naked_triples(): changed=True
            if self._hidden_triples(): changed=True

            if self._assign_from_singletons(): changed=True

        solved = sum(1 for v in self.board if v is not None)
        return self.board[:], solved, (solved==self.N)

# =========================
# Motor de níveis: CHUTE → Regras
# =========================

@dataclass
class LevelState:
    board_before: List[Optional[int]]
    cell: int
    candidates: List[int]
    next_idx: int
    value_fixed: Optional[int] = None

class LevelEngine:
    def __init__(self, width, height, layout, givens):
        self.w, self.h = width, height
        self.N = width*height
        self.layout = layout
        self.board = givens[:]

        self.regions = {}
        for i,ch in enumerate(layout):
            self.regions.setdefault(ch, []).append(i)
        self.neigh = {}
        for i in range(self.N):
            r,c = i2rc(i, width); ns=[]
            for dr in (-1,0,1):
                for dc in (-1,0,1):
                    if dr==0 and dc==0: continue
                    rr,cc = r+dr, c+dc
                    if 0<=rr<height and 0<=cc<width: ns.append(rc2i(rr,cc,width))
            self.neigh[i]=ns

        # autoria das casas
        self.givens_mask = [v is not None for v in self.board]
        self.det_set: set[int] = set()     # por regras (atual)
        self.guess_set: set[int] = set()   # por backtracking (níveis)

        self.levels: List[LevelState] = []
        self.backtracks = 0

    # --- domínios / MRV / checks ---

    def compute_domains(self, board):
        doms = [set() for _ in range(self.N)]
        for i in range(self.N):
            if board[i] is not None:
                doms[i] = {board[i]}
            else:
                size = len(self.regions[self.layout[i]])
                poss = set(range(1, size+1))
                for j in self.regions[self.layout[i]]:
                    v = board[j]
                    if v is not None: poss.discard(v)
                for n in self.neigh[i]:
                    v = board[n]
                    if v is not None: poss.discard(v)
                doms[i] = poss
        return doms

    def violates_constraints(self, board) -> bool:
        # duplicatas na região
        for ch, cells in self.regions.items():
            vals = [board[i] for i in cells if board[i] is not None]
            if len(vals) != len(set(vals)):
                return True
        # vizinhos iguais
        for i in range(self.N):
            v = board[i]
            if v is None: continue
            for n in self.neigh[i]:
                if n < i:  # evita dupla contagem
                    continue
                if board[n] == v:
                    return True
        return False

    def is_complete_and_valid(self, board) -> bool:
        if any(v is None for v in board):
            return False
        return not self.violates_constraints(board)

    def has_contradiction(self, board) -> bool:
        if self.violates_constraints(board):
            return True
        doms = self.compute_domains(board)
        for i in range(self.N):
            if board[i] is None and len(doms[i]) == 0:
                return True
        return False

    def select_mrv_cell(self, board) -> Optional[int]:
        doms = self.compute_domains(board)
        best=None; blen=10**9
        for i in range(self.N):
            if board[i] is None:
                l=len(doms[i])
                if l==0:
                    return i
                if l<blen:
                    blen=l; best=i
        return best

    # --- botão "Resolver (Regras Det)" ---
    def apply_rules(self) -> Tuple[List[int], bool]:
        before = self.board[:]
        solver = DeterministicSolver(self.w, self.h, self.layout, self.board)
        final, _, _ = solver.solve()
        self.board = final
        new_idxs = [i for i,(b,a) in enumerate(zip(before, final)) if b is None and a is not None]
        for i in new_idxs:
            if not self.givens_mask[i]:
                self.det_set.add(i)
        fully = self.is_complete_and_valid(self.board)
        return new_idxs, fully

    # --- ciclo de 1 nível (BT + Regras) ---
    def _commit_try(self, base_board, cell, val) -> Tuple[bool, List[int], List[Optional[int]], bool, dict]:
        test_board = base_board[:]
        test_board[cell] = val
        if self.violates_constraints(test_board):
            return False, [], base_board, False, {"type":"contradiction","cell":cell,"value":val,"reason":"immediate_violation"}

        solver = DeterministicSolver(self.w, self.h, self.layout, test_board)
        new_board, _, _ = solver.solve()

        if self.has_contradiction(new_board):
            return False, [], base_board, False, {"type":"contradiction","cell":cell,"value":val,"reason":"after_rules"}

        det_new = [i for i,(b,a) in enumerate(zip(base_board, new_board)) if b is None and a is not None and i!=cell]
        fully = self.is_complete_and_valid(new_board)
        return True, det_new, new_board, fully, {"type":"commit","cell":cell,"value":val}

    def one_level(self) -> Tuple[str, Dict]:
        if self.is_complete_and_valid(self.board):
            return "solved", {"new_det": [], "level": len(self.levels), "events":[{"type":"solved"}]}

        cell = self.select_mrv_cell(self.board)
        if cell is None:
            return "unsat", {"new_det": [], "level": len(self.levels), "events":[{"type":"unsat"}]}

        base_board = self.board[:]
        doms = self.compute_domains(base_board)
        cand_list = sorted(doms[cell])
        total_bros = len(cand_list)

        events = []
        events.append({"type":"mrv","cell":cell,"cands":cand_list})

        # tenta irmãos no novo nível
        for k, val in enumerate(cand_list):
            ok, det_new, new_board, fully, ev = self._commit_try(base_board, cell, val)
            if not ok:
                events.append(ev)
                continue
            self.board = new_board
            for i in det_new:
                if not self.givens_mask[i]:
                    self.det_set.add(i)
            self.guess_set.add(cell)

            self.levels.append(LevelState(
                board_before=base_board,
                cell=cell,
                candidates=cand_list,
                next_idx=k+1,
                value_fixed=val
            ))
            if det_new:
                events.append({"type":"det_fills","count":len(det_new),"indices":det_new})
            return "level_committed", {
                "probe_cell": cell,
                "new_det": det_new,
                "level": len(self.levels),
                "cell": cell,
                "value": val,
                "brother_pos": (k+1, total_bros),
                "fully": fully,
                "events": events + [ev]
            }

        # retrocesso
        while self.levels:
            top = self.levels.pop()

            prev_board = self.board[:]
            self.backtracks += 1
            self.board = top.board_before[:]

            reverted = [i for i,(a,b) in enumerate(zip(prev_board, self.board)) if a != b]
            for i in reverted:
                if i in self.det_set and not self.givens_mask[i]:
                    self.det_set.discard(i)
            if top.cell in self.guess_set:
                self.guess_set.discard(top.cell)

            events.append({"type":"rollback","reverted":reverted,"from_cell":top.cell})

            j = len(top.candidates)
            for k in range(top.next_idx, j):
                val = top.candidates[k]
                ok, det_new2, new_board2, fully2, ev2 = self._commit_try(top.board_before, top.cell, val)
                if not ok:
                    events.append(ev2)
                    continue
                self.board = new_board2
                for i in det_new2:
                    if not self.givens_mask[i]:
                        self.det_set.add(i)
                self.guess_set.add(top.cell)

                self.levels.append(LevelState(
                    board_before=top.board_before,
                    cell=top.cell,
                    candidates=top.candidates,
                    next_idx=k+1,
                    value_fixed=val
                ))
                if det_new2:
                    events.append({"type":"det_fills","count":len(det_new2),"indices":det_new2})
                return "level_committed", {
                    "probe_cell": top.cell,
                    "new_det": det_new2,
                    "level": len(self.levels),
                    "cell": top.cell,
                    "value": val,
                    "brother_pos": (k+1, j),
                    "fully": fully2,
                    "reverted": reverted,
                    "events": events + [ev2]
                }

        events.append({"type":"unsat"})
        return "unsat", {"probe_cell": cell, "new_det": [], "level": 0, "events": events}

    # ---------- métricas para UI ----------
    def det_count(self) -> int:
        return len(self.det_set)

    def guess_count(self) -> int:
        return len(self.guess_set)

    def givens_count(self) -> int:
        return sum(1 for v in self.givens_mask if v)

    def filled_total(self) -> int:
        return sum(1 for v in self.board if v is not None)

# =========================
# GUI
# =========================

DEFAULT_FILES = {
    "6x6":      "SUG_6x6_v12.txt",
    "8x8":      "SUG_8x8_v12.txt",
    "12x10":    "SUG_12x10_v12.txt",
    "15x10":    "SUG_15x10_v12.txt",
    "15x10 n=6":"SUG_15x10n6_v12.txt",
}

class SuguruLevelsGUI:
    def __init__(self, root, initial_puzzles, initial_size_label="8x8", initial_path=None):
        self.root = root
        self.root.title("Suguru — Níveis: Chute + Regras (animado)                         By Michele")

        # estado geral
        self.puzzles = initial_puzzles
        self.current = None
        self.width = 8
        self.height = 8
        self.layout = None
        self.engine: Optional[LevelEngine] = None
        self.board = None
        self.givens_mask = None
        self.regions = None

        # badges persistentes por célula
        self.level_badges: Dict[int, int] = {}
        self.autorun_flag = False
        self.delay_ms = 50

        # UI raiz
        main = ttk.Frame(root, padding=8)
        main.pack(fill="both", expand=True)

        # ===== TOPO: controles de tamanho/arquivo =====
        toolbar = ttk.Frame(main)
        toolbar.pack(fill="x", pady=(0,6))

        ttk.Label(toolbar, text="Tamanho:").pack(side="left")
        self.size_var = tk.StringVar(value=initial_size_label)
        self.size_combo = ttk.Combobox(toolbar, width=10, textvariable=self.size_var,
                                       values=list(DEFAULT_FILES.keys()), state="readonly")
        self.size_combo.pack(side="left", padx=6)
        self.size_combo.bind("<<ComboboxSelected>>", self.on_size_change)

        ttk.Label(toolbar, text="Arquivo:").pack(side="left", padx=(16,4))
        self.path_var = tk.StringVar(value=initial_path or DEFAULT_FILES.get(initial_size_label, "SUG_8x8_v12.txt"))
        self.path_entry = ttk.Entry(toolbar, width=38, textvariable=self.path_var)
        self.path_entry.pack(side="left")
        ttk.Button(toolbar, text="Abrir outro arquivo…", command=self.pick_file).pack(side="left", padx=6)
        ttk.Button(toolbar, text="Recarregar", command=self.reload_from_path).pack(side="left")

        # ===== Esquerda: lista + histórico =====
        left = ttk.Frame(main)
        left.pack(side="left", fill="y")

        ttk.Label(left, text="Puzzles").pack(anchor="w")
        self.listbox = tk.Listbox(left, height=14, width=30)
        self.listbox.pack(fill="y")
        self.listbox.bind("<<ListboxSelect>>", self.on_select)

        # Ir para ID
        goto = ttk.Frame(left)
        goto.pack(pady=6, fill="x")
        ttk.Label(goto, text="Ir para ID:").pack(side="left")
        self.id_entry = ttk.Entry(goto, width=8)
        self.id_entry.pack(side="left", padx=4)
        ttk.Button(goto, text="Ir", command=self.go_to_id).pack(side="left")
        self.id_entry.bind("<Return>", lambda e: self.go_to_id())

        # HISTÓRICO
        ttk.Label(left, text="Histórico").pack(anchor="w", pady=(8,2))
        hist_frame = ttk.Frame(left)
        hist_frame.pack(fill="both", expand=True)
        self.history = tk.Text(hist_frame, height=18, width=30, wrap="word")
        self.history.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(hist_frame, orient="vertical", command=self.history.yview)
        sb.pack(side="right", fill="y")
        self.history.configure(yscrollcommand=sb.set)
        self.history.tag_configure("mrv", foreground="#6c757d")
        self.history.tag_configure("try", foreground="#343a40")
        self.history.tag_configure("det", foreground="#198754")
        self.history.tag_configure("commit", foreground="#0d6efd")
        self.history.tag_configure("rollback", foreground="#fd7e14")
        self.history.tag_configure("contradiction", foreground="#dc3545", font=("Arial", 10, "bold"))
        self.history.tag_configure("done", foreground="#20c997")

        hist_btns = ttk.Frame(left)
        hist_btns.pack(fill="x", pady=4)
        ttk.Button(hist_btns, text="Limpar histórico", command=self.clear_history).pack(side="left")
        ttk.Button(hist_btns, text="Salvar histórico", command=self.save_history).pack(side="right")

        # ===== Direita: tabuleiro + controles =====
        right = ttk.Frame(main)
        right.pack(side="right", fill="both", expand=True)

        # canvas + dimensões dinâmicas
        self.canvas = tk.Canvas(right, width=520, height=520, bg="white", highlightthickness=0)
        self.canvas.pack(pady=4)
        self.margin = 20
        self.cell_size = 60  # recalculado a cada puzzle

        controls = ttk.Frame(right)
        controls.pack(fill="x", pady=6)

        self.btn_det = ttk.Button(controls, text="Resolver (Regras Det)", command=self.apply_det_rules)
        self.btn_det.grid(row=0, column=0, padx=4)

        self.btn_one = ttk.Button(controls, text="1 Nível (BT + Regras)", command=self.run_one_level)
        self.btn_one.grid(row=0, column=1, padx=4)

        self.btn_auto = ttk.Button(controls, text="Auto-run", command=self.autorun_start)
        self.btn_auto.grid(row=0, column=2, padx=4)

        self.btn_stop = ttk.Button(controls, text="Parar", command=self.autorun_stop)
        self.btn_stop.grid(row=0, column=3, padx=4)

        self.btn_reset = ttk.Button(controls, text="Resetar", command=self.reset_board)
        self.btn_reset.grid(row=0, column=4, padx=4)

        # Velocidade
        self.min_delay = 5
        self.max_delay = 250
        self.speed_scale = ttk.Scale(controls, from_=0, to=100, value=50, orient="horizontal", command=self.on_speed)
        ttk.Label(controls, text="Velocidade").grid(row=0, column=5, padx=(20,4))
        self.speed_scale.grid(row=0, column=6, padx=4, sticky="ew")
        controls.columnconfigure(6, weight=1)

        # Status
        self.status = tk.StringVar(value="Selecione um puzzle.")
        ttk.Label(right, textvariable=self.status).pack(anchor="w", pady=(4,0))

        # carrega lista inicial
        self.populate_listbox()

        # auto-seleciona primeiro
        if self.puzzles:
            self.listbox.selection_set(0)
            self.on_select()

    # ---------- suporte multi-arquivo/tamanho ----------

    def recompute_cell_size(self):
        # tenta caber dentro de ~720px em cada dimensão
        target = 720
        s_w = (target - 2*self.margin) / max(1, self.width)
        s_h = (target - 2*self.margin) / max(1, self.height)
        self.cell_size = int(max(22, min(60, s_w, s_h)))  # limites razoáveis

    def on_size_change(self, event=None):
        size_label = self.size_var.get()
        default_path = DEFAULT_FILES.get(size_label, "")
        if default_path:
            # só substitui se o usuário não customizou manualmente outro caminho para esse tamanho
            self.path_var.set(default_path if os.path.exists(default_path) or True else self.path_var.get())
        self.reload_from_path()

    def pick_file(self):
        path = filedialog.askopenfilename(
            title="Abrir arquivo de instâncias",
            filetypes=[("Texto", "*.txt"), ("Todos", "*.*")]
        )
        if not path:
            return
        self.path_var.set(path)
        self.reload_from_path()

    def reload_from_path(self):
        path = self.path_var.get().strip()
        if not path:
            messagebox.showerror("Erro", "Informe um caminho de arquivo.")
            return
        try:
            puzzles = load_puzzles(path)
        except Exception as e:
            messagebox.showerror("Erro", f"Falha ao ler {path}:\n{e}")
            return

        self.puzzles = puzzles
        self.populate_listbox()
        if self.puzzles:
            self.listbox.selection_clear(0, "end")
            self.listbox.selection_set(0)
            self.on_select()
            self.log(f"Arquivo carregado: {os.path.basename(path)}", "mrv")
        else:
            self.clear_history()
            self.log("Arquivo sem puzzles válidos.", "contradiction")

    def populate_listbox(self):
        self.listbox.delete(0, "end")
        pat_work = re.compile(r'work=(\d+)')
        for p in self.puzzles:
            m = pat_work.search(p.get("comment",""))
            work = f" (work={m.group(1)})" if m else ""
            self.listbox.insert("end", f'{p["name"]}{work}')

    # ---------- histórico ----------

    def log(self, text: str, tag: Optional[str]=None):
        self.history.insert("end", text + "\n", (tag,) if tag else ())
        self.history.see("end")

    def clear_history(self):
        self.history.delete("1.0", "end")

    def save_history(self):
        path = filedialog.asksaveasfilename(
            title="Salvar histórico",
            defaultextension=".log",
            filetypes=[("Log", "*.log"), ("Texto", "*.txt"), ("Todos", "*.*")]
        )
        if not path:
            return
        try:
            content = self.history.get("1.0", "end-1c")
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
            messagebox.showinfo("OK", f"Histórico salvo em:\n{path}")
        except Exception as e:
            messagebox.showerror("Erro", f"Falha ao salvar histórico:\n{e}")

    # ---------- navegação ID ----------

    def go_to_id(self):
        raw = self.id_entry.get().strip()
        if not raw:
            return
        if raw.lower().startswith("suguru-"):
            raw = raw.split("-",1)[1]
        if not raw.isdigit():
            messagebox.showerror("ID inválido", "Digite apenas o número (ex.: 42) ou 'Suguru-42'.")
            return
        target = int(raw)
        pat = re.compile(r'.*-(\d+)$')
        for idx,p in enumerate(self.puzzles):
            m = pat.match(p["name"])
            if m and int(m.group(1))==target:
                self.listbox.selection_clear(0,"end")
                self.listbox.selection_set(idx)
                self.listbox.see(idx)
                self.on_select()
                return
        messagebox.showinfo("Não encontrado", f"Não encontrei 'Suguru-{target}'.")

    # ---------- helpers UI ----------

    def on_speed(self, val):
        try:
            v = float(val)
        except:
            v = 50.0
        self.delay_ms = int(self.max_delay - (self.max_delay - self.min_delay) * (v / 100.0))

    def set_status(self, text):
        self.status.set(text)

    def _build_regions(self):
        self.regions = {}
        for i, ch in enumerate(self.layout):
            self.regions.setdefault(ch, []).append(i)

    def flash_cell(self, idx, color="#fff3b0", ms=120):
        r, c = i2rc(idx, self.width)
        s = self.cell_size; m = self.margin
        x1 = m + c*s; y1 = m + r*s
        x2 = x1 + s;  y2 = y1 + s
        rect = self.canvas.create_rectangle(x1+2, y1+2, x2-2, y2-2, fill=color, outline="")
        self.root.update_idletasks()
        self.root.after(ms, lambda: self.canvas.delete(rect))

    def draw_board(self):
        # recalcula tamanho da célula p/ caber confortavelmente
        self.recompute_cell_size()

        self.canvas.delete("all")
        s = self.cell_size
        m = self.margin
        W = m*2 + s*self.width
        H = m*2 + s*self.height
        self.canvas.config(width=W, height=H)

        # finas internas
        for r in range(self.height):
            for c in range(self.width):
                x1 = m + c*s
                y1 = m + r*s
                x2 = x1 + s
                y2 = y1 + s
                if c>0:
                    self.canvas.create_line(x1, y1, x1, y2, fill="#cccccc", width=1)
                if r>0:
                    self.canvas.create_line(x1, y1, x2, y1, fill="#cccccc", width=1)
        # borda externa grossa
        self.canvas.create_rectangle(m, m, m+s*self.width, m+s*self.height, width=3)

        # bordas de regiões grossas
        for r in range(self.height):
            for c in range(self.width):
                i = rc2i(r,c,self.width)
                ch = self.layout[i]
                x1 = m + c*s; y1 = m + r*s
                x2 = x1 + s;  y2 = y1 + s
                if c==0 or self.layout[i-1]!=ch:
                    self.canvas.create_line(x1, y1, x1, y2, width=3)
                if c==self.width-1 or self.layout[i+1]!=ch:
                    self.canvas.create_line(x2, y1, x2, y2, width=3)
                if r==0 or self.layout[i-self.width]!=ch:
                    self.canvas.create_line(x1, y1, x2, y1, width=3)
                if r==self.height-1 or self.layout[i+self.width]!=ch:
                    self.canvas.create_line(x1, y2, x2, y2, width=3)

        for i, v in enumerate(self.board):
            self.draw_value(i, v, tentative=False)

        self.redraw_badges()
        self.redraw_pencilmarks()

    def draw_value(self, idx, val, tentative=False, color_override=None):
        r, c = i2rc(idx, self.width)
        s = self.cell_size; m = self.margin
        x = m + c*s + s/2
        y = m + r*s + s/2
        self.canvas.delete(f"text_{idx}")
        if val is None:
            return
        color = color_override or ("#444444" if self.givens_mask[idx] else ("#888888" if tentative else "#000000"))
        self.canvas.create_text(x, y, text=str(val), font=("Arial", int(s*0.45), "bold"),
                                fill=color, tags=f"text_{idx}")

    def set_badge_level(self, idx, level_k: Optional[int]):
        # persistência de estado
        if level_k is None:
            self.level_badges.pop(idx, None)
        else:
            self.level_badges[idx] = level_k

        # redesenha apenas essa célula
        self.canvas.delete(f"badge_{idx}")
        if level_k is None:
            return
        r, c = i2rc(idx, self.width)
        s = self.cell_size; m = self.margin
        x1 = m + c*s + 6
        y1 = m + r*s + 10
        self.canvas.create_text(x1, y1, text=f"B{level_k}", anchor="w",
                                font=("Arial", max(10, int(s*0.22)), "bold"),
                                fill="#0d6efd", tags=f"badge_{idx}")

    def redraw_badges(self):
        # limpa tudo e repinta do dicionário persistido
        for i in range(self.width*self.height):
            self.canvas.delete(f"badge_{i}")
        for idx, lvl in self.level_badges.items():
            self.set_badge_level(idx, lvl)

    def redraw_pencilmarks(self):
        for i in range(self.width * self.height):
            self.canvas.delete(f"pencil_{i}")

        doms = self.engine.compute_domains(self.board) if self.engine else [set() for _ in range(self.width*self.height)]
        s = self.cell_size; m = self.margin
        font_sz = max(8, int(s*0.18))

        # posições para 1..6 (grade 3x2)
        pos_map = {
            1:(0,0), 2:(1,0), 3:(2,0),
            4:(0,1), 5:(1,1), 6:(2,1),
        }

        for i in range(self.width*self.height):
            if self.board[i] is not None:
                continue
            if self.givens_mask[i]:
                continue
            r, c = i2rc(i, self.width)
            x0 = m + c*s
            y0 = m + r*s
            for d in sorted(doms[i]):
                if d not in pos_map:
                    # para regiões maiores que 6 (improvável aqui), omite visual de pencil extra
                    continue
                px, py = pos_map[d]
                dx = (s/8) + px*(s/3)   # leve ajuste p/ caber 3x2
                dy = (s/8) + py*(s/2.6)
                self.canvas.create_text(
                    x0 + dx, y0 + dy, text=str(d),
                    font=("Arial", font_sz),
                    fill="#b0b0b0",
                    tags=f"pencil_{i}",
                    anchor="center"
                )

    # ---------- eventos ----------

    def on_select(self, event=None):
        sel = self.listbox.curselection()
        if not sel:
            return
        self.current = self.puzzles[sel[0]]
        self.width  = self.current["width"]
        self.height = self.current["height"]
        self.layout = self.current["layout"]

        self.engine = LevelEngine(self.width, self.height, self.layout, self.current["givens"])
        self.board = self.engine.board
        self.givens_mask = [v is not None for v in self.board]
        self._build_regions()
        self.level_badges.clear()
        self.autorun_flag = False
        self.draw_board()
        self.clear_history()
        self.log(f"Carregado: {self.current['name']}", "mrv")
        self.update_status("Pronto.")

    def reset_board(self):
        if not self.current: return
        self.engine = LevelEngine(self.width, self.height, self.layout, self.current["givens"])
        self.board = self.engine.board
        self.givens_mask = [v is not None for v in self.board]
        self.level_badges.clear()
        self.autorun_flag = False
        self.draw_board()
        self.clear_history()
        self.log("Tabuleiro resetado.", "mrv")
        self.update_status("Tabuleiro resetado.")

    def update_status(self, extra=""):
        det_now = self.engine.det_count() if self.engine else 0
        guess_now = self.engine.guess_count() if self.engine else 0
        givens_now = self.engine.givens_count() if self.engine else 0
        filled = self.engine.filled_total() if self.engine else 0
        lvl = len(self.engine.levels) if self.engine else 0
        bt = self.engine.backtracks if self.engine else 0
        msg = (f"Dicas: {givens_now} | Det: {det_now} | BT: {guess_now} | "
               f"Preenchidas: {filled}/{self.width*self.height} | Nível BT: {lvl} | Retrocessos: {bt}")
        if extra: msg += f" — {extra}"
        self.set_status(msg)

    # ---------- rollback visual ----------

    def apply_rollback_visual(self, reverted_indices: List[int]):
        if not reverted_indices:
            return
        for i in reverted_indices:
            self.canvas.delete(f"text_{i}")
            v = self.engine.board[i]
            if v is not None:
                self.draw_value(i, v, tentative=False)
        self.redraw_pencilmarks()
        for i in reverted_indices:
            self.flash_cell(i, color="#ffe3e3", ms=90)

    # ---------- ações ----------

    def animate_new_dets(self, indices: List[int]):
        if indices:
            self.log(f"Deduções determinísticas: +{len(indices)}", "det")
        for i in indices:
            self.draw_value(i, self.engine.board[i], tentative=False, color_override="#000000")
            self.flash_cell(i, "#ddffdd", ms=80)
            self.root.update()
            self.root.after(self.delay_ms)
        self.redraw_pencilmarks()

    def color_guess_cell(self, cell_idx: int, level_k: int, val: int):
        self.draw_value(cell_idx, val, tentative=False, color_override="#0d6efd")
        self.set_badge_level(cell_idx, level_k)
        self.root.update()
        self.redraw_pencilmarks()
        r,c = i2rc(cell_idx, self.width)
        self.log(f"Nível {level_k} fixado em ({r+1},{c+1}) = {val}", "commit")

    def highlight_probe_cell(self, idx: Optional[int], cand_list: Optional[List[int]]=None):
        if idx is None:
            return
        self.flash_cell(idx, color="#fff3b0", ms=160)
        r,c = i2rc(idx, self.width)
        if cand_list is not None:
            self.log(f"MRV ({r+1},{c+1}) candidatos: {cand_list}", "mrv")
        else:
            self.log(f"MRV em ({r+1},{c+1})", "mrv")

    def apply_det_rules(self):
        if not self.engine: return
        new_idxs, fully = self.engine.apply_rules()
        self.board = self.engine.board
        self.animate_new_dets(new_idxs)
        self.redraw_pencilmarks()
        if fully:
            self.update_status("Resolvido por regras determinísticas.")
        else:
            self.update_status("Regras aplicadas (manual).")

    def process_events_log(self, events: List[dict]):
        for ev in events or []:
            t = ev.get("type")
            if t == "mrv":
                cell = ev.get("cell")
                cands = ev.get("cands", [])
                if cell is not None:
                    self.highlight_probe_cell(cell, cands)
            elif t == "contradiction":
                cell = ev.get("cell"); val = ev.get("value")
                r,c = i2rc(cell, self.width) if cell is not None else ("?","?")
                reason = ev.get("reason","")
                self.log(f"Contradição em candidato ({r+1},{c+1})={val} [{reason}]", "contradiction")
            elif t == "rollback":
                rev = ev.get("reverted", [])
                from_cell = ev.get("from_cell")
                self.log(f"Rollback: revertidas {len(rev)} casas", "rollback")
                # remove badge do nível desfeito
                if from_cell is not None:
                    self.set_badge_level(from_cell, None)
            elif t == "det_fills":
                cnt = ev.get("count",0)
                self.log(f"Deduções determinísticas: +{cnt}", "det")
            elif t == "commit":
                cell = ev.get("cell"); val = ev.get("value")
                r,c = i2rc(cell, self.width) if cell is not None else ("?","?")
                self.log(f"Commit candidato ({r+1},{c+1})={val}", "commit")
            elif t == "solved":
                self.log("Resolvido.", "done")
            elif t == "unsat":
                self.log("Sem solução (unsat).", "contradiction")

    def run_one_level(self):
        if not self.engine: return

        # pré-visualização do MRV atual
        probe = self.engine.select_mrv_cell(self.engine.board)
        if probe is not None:
            pre_doms = self.engine.compute_domains(self.engine.board)
            self.highlight_probe_cell(probe, sorted(pre_doms[probe]))

        status, info = self.engine.one_level()
        self.board = self.engine.board

        self.process_events_log(info.get("events", []))

        reverted = info.get("reverted", [])
        if reverted:
            self.apply_rollback_visual(reverted)

        new_det = info.get("new_det", [])
        self.animate_new_dets(new_det)

        if status == "solved":
            self.update_status("Resolvido.")
            self.draw_board()  # badges persistem
            return
        if status == "unsat":
            self.update_status("Sem solução (esgotou alternativas).")
            return
        if status == "level_committed":
            cell = info["cell"]
            val  = info["value"]
            level_k = info["level"]
            i,j = info["brother_pos"]
            self.color_guess_cell(cell, level_k, val)
            self.flash_cell(cell, "#dde7ff", ms=120)
            extra = f"Nível {level_k} fixado ({i}/{j})."
            if info.get("fully"):
                extra += " (tabuleiro completo após regras)"
            self.update_status(extra)

    # ---------- Auto-run ----------

    def autorun_start(self):
        if not self.engine: return
        if self.autorun_flag: return
        self.autorun_flag = True
        self.update_status("Auto-run iniciado.")
        self._autorun_tick()

    def autorun_stop(self):
        self.autorun_flag = False
        self.update_status("Auto-run parado.")

    def _autorun_tick(self):
        if not self.autorun_flag: return

        # (0) REGRAS DETERMINÍSTICAS PRIMEIRO
        new_idxs, fully = self.engine.apply_rules()
        self.board = self.engine.board
        if new_idxs:
            self.animate_new_dets(new_idxs)
            self.redraw_pencilmarks()
            if fully:
                self.log("Auto: resolvido por regras determinísticas.", "done")
                self.update_status("Auto: resolvido.")
                self.draw_board()  # badges persistem
                return
            self.root.after(self.delay_ms, self._autorun_tick)
            return

        # (1) TRAVOU -> 1 nível (BT + Regras)
        status, info = self.engine.one_level()
        self.board = self.engine.board

        self.process_events_log(info.get("events", []))

        reverted = info.get("reverted", [])
        if reverted:
            self.apply_rollback_visual(reverted)

        new_det = info.get("new_det", [])
        self.animate_new_dets(new_det)

        if status == "level_committed":
            cell = info["cell"]; val = info["value"]; level_k = info["level"]
            i,j = info["brother_pos"]
            self.color_guess_cell(cell, level_k, val)
            self.flash_cell(cell, "#dde7ff", ms=80)
            extra = f"Auto: nível {level_k} fixado ({i}/{j})."
            if info.get("fully"):
                extra += " (completo)"
            self.update_status(extra)
        elif status == "solved":
            self.log("Auto: resolvido.", "done")
            self.update_status("Auto: resolvido.")
            self.draw_board()  # badges persistem
            return
        elif status == "unsat":
            self.log("Auto: sem solução (unsat).", "contradiction")
            self.update_status("Auto: sem solução (esgotou alternativas).")
            return

        self.root.after(self.delay_ms, self._autorun_tick)

# =========================
# Main
# =========================

def guess_initial_size_label(path: str) -> str:
    nm = os.path.basename(path).lower()
    if "6x6" in nm: return "6x6"
    if "8x8" in nm: return "8x8"
    if "12x10" in nm and "n6" not in nm: return "12x10"
    if "15x10n6" in nm: return "15x10 n=6"
    if "15x10" in nm: return "15x10"
    return "8x8"

def main():
    # tenta um arquivo padrão inicial (8x8)
    default_path = DEFAULT_FILES.get("8x8", "SUG_8x8_v12.txt")
    try:
        puzzles = load_puzzles(default_path)
    except Exception:
        puzzles = []
    root = tk.Tk()
    size_label = guess_initial_size_label(default_path)
    app = SuguruLevelsGUI(root, puzzles, initial_size_label=size_label, initial_path=default_path)
    root.mainloop()

if __name__ == "__main__":
    main()
