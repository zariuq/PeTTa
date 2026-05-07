; Cyclic HE imports should surface ModuleImportCycle and keep the target space
; rolled back to the pre-import state.

(base)
!(assertEqualToResult
  (collapse (import! &self support/import_cycle/A.metta))
  (((Error (import! &self support/import_cycle/A.metta)
            (Error (import! &self B)
                   (Error (import! &self A)
                          (ModuleImportCycle "support/import_cycle/A.metta")))))))
!(assertEqual (collapse (match &self (base) (base))) ((base)))
!(assertEqual (collapse (match &self (cycle-a-before) (cycle-a-before))) ())
!(assertEqual (collapse (match &self (cycle-b-before) (cycle-b-before))) ())
