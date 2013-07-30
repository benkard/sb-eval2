(defpackage "SB-EVAL2"
  (:use "COMMON-LISP")
  (:shadow "EVAL" "LOAD" "INSTALL")
  (:export "EVAL" "LOAD" "INSTALL"))

(in-package "SB-EVAL2")

;;(declaim (optimize (debug 3) (space 0) (speed 0) (safety 3) (compilation-speed 0)))
(declaim (optimize (debug 0) (space 0) (speed 3) (safety 0) (compilation-speed 0)))

(defconstant +stack-max+ 8)

(defvar *mode* :not-compile-time)
(defvar *form*)
(defvar *source-paths* (make-hash-table :weakness :key :test #'eq))
(defvar *source-info* (make-hash-table :weakness :key :test #'eq))
(defvar *source-locations* (make-hash-table :weakness :key :test #'eq))
(defvar *closure-tags* (make-hash-table :weakness :key :test #'eq))

(defmacro specialize (var value possible-values &body body)
  `(ecase ,value
     ,@(loop for x in (cl:eval possible-values)
             collect
                `((,x) ,(cl:eval `(let ((,var ,x)) ,@body))))))

(declaim (inline %make-environment))
(defstruct (environment (:constructor %make-environment))
  (parent nil :type (or null environment))
  (data nil :type (or null simple-vector)))

(declaim (inline make-null-environment))
(defun make-null-environment () (make-environment nil 0))

(declaim (inline make-environment))
(defun make-environment (parent
                         &optional (size 0)
                         &aux (data
                               (unless (zerop (the fixnum size))
                                 (make-array
                                  (list size)))))
  (%make-environment :parent parent :data data))

(defmacro with-dynamic-extent-environment ((var parent size) &body body)
  (let ((data% (gensym))
        (size% (gensym)))
    `(let* ((,size% ,size)
            (,data% (make-array (list ,size%)))
            (,var (%make-environment :parent ,parent :data ,data%)))
       (declare (type (mod #.(1+ +stack-max+)) ,size%)
                ;; we must not allocate environment objects on the
                ;; stack unless we can be sure that all child
                ;; environments will also be allocated on the stack,
                ;; but we can't really know that.
                ;(dynamic-extent ,var)
                (dynamic-extent ,data%))
       ,@body)))

(defclass lexical ()
  ((name    :accessor lexical-name    :initarg :name    :type (or symbol list))))

(defclass env-lexical (lexical)
  ((offset  :accessor lexical-offset  :initarg :offset  :type fixnum)
   (nesting :accessor lexical-nesting :initarg :nesting :type fixnum)))

(defun make-env-lexical (name offset &optional (nesting -1))
  (make-instance 'env-lexical :name name :offset offset :nesting nesting))

(defun lexical-with-nesting (lexical nesting)
  (make-env-lexical (lexical-name lexical) (lexical-offset lexical) nesting))

(defun maybe-references-p/env (form vars env)
  ;; Use `(function ,name) for local functions.
  ;;
  ;; FIXME: This doesn't do macro expansion, so it's probably
  ;; incorrect.
  (let ((sb-walker::*walk-form-expand-macros-p* t))
    (sb-walker:walk-form
     form
     env
     (lambda (x ctx env)
       (declare (ignore ctx))
       (when (and (member x vars :test #'equal)
                  (not (sb-walker:var-special-p x env))
                  (not (sb-walker:var-lexical-p x env)))
         (return-from maybe-references-p/env t))
       x)))
  nil)

(defun maybe-closes-over-p (context form vars)
  (handler-case
      (maybe-closes-over-p/env form vars (context->native-environment context))
    (serious-condition () t)))

(defun maybe-closes-over-p/env (form vars env)
  (let ((sb-walker::*walk-form-expand-macros-p* t))
    (sb-walker:walk-form
     form
     env
     (lambda (x ctx env)
       (declare (ignore ctx))
       (typecase x
         (cons
          (destructuring-bind (a . b) x
            (case a
              ((lambda sb-int:named-lambda)
               (when (maybe-references-p/env form vars env)
                 (return-from maybe-closes-over-p/env t)))
              ((flet labels)
               (typecase b
                 (cons
                  (destructuring-bind (bindings . rest) form
                    (when (or (maybe-references-p/env bindings vars env)
                              (maybe-closes-over-p/env rest vars env))
                      (return-from maybe-closes-over-p/env t))))
                 (t
                  (when (maybe-closes-over-p/env b vars env)
                    (return-from maybe-closes-over-p/env t)))))))))
       x)))
  nil)

(defstruct (context (:constructor make-context (&optional parent)))
  parent
  (env-hop nil :type boolean)
  (block-tags nil :type list)
  (go-tags nil :type list)
  (symbol-macros nil :type list)
  (macros nil :type list)
  (lexicals nil :type list)
  (specials nil :type list))
(defun make-null-context ()
  (make-context nil))
(defun context-add-block-tag (context block tag)
  (let ((new-context (make-context context)))
    (with-slots (block-tags)
        new-context
      (setq block-tags (acons block tag block-tags)))
    new-context))
(defun context-block-tag (context block)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the symbol block) (context-block-tags context)))
        (and parent (context-block-tag parent block)))))
(defun context-add-go-tags (context new-go-tags catch-tag)
  (let ((new-context (make-context context)))
    (with-slots (go-tags)
        new-context
      (dolist (new-go-tag new-go-tags)
        (setq go-tags (acons new-go-tag catch-tag go-tags))))
    new-context))
(defun context-collect (context f)
  (let ((parent (context-parent context)))
    (append (funcall f context) (and parent (context-collect parent f)))))
(defun context-find-go-tag (context go-tag)
  (let ((parent (context-parent context)))
    (or (cdr (assoc (the atom go-tag) (context-go-tags context)))
        (and parent (context-find-go-tag parent go-tag)))))
(defun context-find-symbol-macro (context symmac)
  (let ((parent (context-parent context)))
    (and (not (member symmac
                      (context-lexicals context)
                      :test #'equal
                      :key #'lexical-name))
         (not (member symmac (context-specials context) :test #'equal))
         (or (cdr (assoc (the symbol symmac) (context-symbol-macros context)))
             (and parent (context-find-symbol-macro parent symmac))))))
(defun context-find-macro (context mac)
  (let ((parent (context-parent context)))
    (and (not (member `(function ,mac)
                      (context-lexicals context)
                      :test #'equal
                      :key #'lexical-name))
         (or (cdr (assoc (the (or symbol list) mac)
                         (context-macros context)
                         :test #'equal))
             (and parent (context-find-macro parent mac))))))
(defun context-add-symbol-macros (context bindings)
  (let ((new-context (make-context context)))
    (with-slots (symbol-macros)
        new-context
      (setq symbol-macros (append bindings symbol-macros)))
    new-context))
(defun context-add-macros (context bindings)
  (let ((new-context (make-context context)))
    (with-slots (macros)
        new-context
      (setq macros (append bindings macros)))
    new-context))
(defun parse-tagbody-tags-and-bodies (forms)
  (let ((next-form (gensym))
        (finishp nil))
    (loop until finishp
          collect
             (progn
               (unless forms
                 (setq finishp (null forms)))
               (let ((tag next-form)
                     (current-forms (loop for current-form = (pop forms)
                                          do (setq next-form current-form)
                                          until (atom current-form)
                                          collect current-form)))
                 (cons tag current-forms))))))
(defun context-var-symbol-macro-p (context var)
  (and (not (find var (context-specials context) :test #'equal))
       (not (find var (context-lexicals context) :key #'lexical-name :test #'equal))
       (or (find var (context-symbol-macros context) :key #'car :test #'equal)
           (and (context-parent context)
                (context-var-symbol-macro-p (context-parent context) var)))))
(defun context-var-lexical-p (context var)
  (and (not (find var (context-specials context) :test #'equal))
       (not (find var (context-symbol-macros context) :key #'car :test #'equal))
       (or (find var (context-lexicals context) :key #'lexical-name :test #'equal)
           (and (context-parent context)
                (context-var-lexical-p (context-parent context) var)))))
(defun context-var-special-p (context var)
  (and (not (find var (context-lexicals context) :key #'lexical-name :test #'equal))
       (not (find var (context-symbol-macros context) :key #'car :test #'equal))
       (or (find var (context-specials context) :test #'equal)
           (and (context-parent context)
                (context-var-special-p (context-parent context) var)))))
(defun context-add-env-lexicals (context vars)
  ;; open a new variable context
  (let ((new-context (make-context context)))
    (with-slots (lexicals env-hop)
        new-context
      (setq env-hop t)
      (setq lexicals (loop for i fixnum from 0
                           for v in vars
                           collect (make-env-lexical v i))))
    new-context))
(defun make-lexical-context (context)
  (let ((new-context (make-context context)))
    (setf (context-env-hop new-context) t)
    new-context))
(defun context-add-env-lexical! (context var)
  (with-slots (lexicals)
      context
    (push (make-env-lexical var (length lexicals)) lexicals))
  (values))
(defun context-add-specials (context vars)
  (let ((new-context (make-context context)))
    (setf (context-specials new-context) vars)
    new-context))
(defun context-add-special! (context var)
  (with-slots (specials)
      context
    (push var specials))
  (values))
(defun context-add-env-functions (context fs)
  (context-add-env-lexicals context (mapcar (lambda (x) `(function ,x)) fs)))
(defun context-find-lexical (context var)
  (loop with env-level = 0
        until (null context)
        for record = (find var
                           (context-lexicals context)
                           :key #'lexical-name
                           :test #'equal)
        when record
          do (return
               (etypecase record
                 (env-lexical   (lexical-with-nesting record env-level))))
        when (context-env-hop context)
          do (incf env-level)
        do (setq context (context-parent context))))

(deftype eval-closure () `(function (environment) *))

(declaim (inline environment-value))
(defun environment-value (env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (svref (environment-data env) offset))

(declaim (inline (setf environment-value)))
(defun (setf environment-value) (val env nesting offset)
  (dotimes (i (the fixnum nesting))
    (setq env (environment-parent env)))
  (setf (svref (environment-data env) offset) val))


(defun source-path (eval-closure)
  (gethash eval-closure *source-paths*))
(defun source-info (eval-closure)
  (gethash eval-closure *source-info*))
(defun source-location (eval-closure)
  (gethash eval-closure *source-locations*))
(defun (setf source-path) (val eval-closure)
  (setf (gethash eval-closure *source-paths*) val))
(defun (setf source-info) (val eval-closure)
  (setf (gethash eval-closure *source-info*) val))
(defun (setf source-location) (val eval-closure)
  (setf (gethash eval-closure *source-locations*) val))


(defun annotate-lambda-with-source (closure tag)
  (when (and (boundp 'sb-c::*current-path*)
             (boundp 'sb-c::*source-info*))
    (setf (source-path tag) sb-c::*current-path*)
    (setf (source-info tag) sb-c::*source-info*)
    (setf (source-location tag) (sb-c::make-definition-source-location)))
  closure)

(defmacro eval-lambda (lambda-list &body body)
  (let ((gtag (gensym)))
    `(let ((,gtag (gensym)))
       (annotate-lambda-with-source
        (let ((%%%eval-closure-tag ,gtag))
          (declare (ignorable %%%eval-closure-tag))
          (assert (symbolp %%%eval-closure-tag))
          (sb-int:named-lambda eval-closure
            ,lambda-list ,@body))
        ,gtag))))


(declaim (ftype (function (symbol context) eval-closure) prepare-ref))
(defun prepare-ref (var context)
  (if (context-var-lexical-p context var)
      (let* ((lexical (context-find-lexical context var))
             (nesting (lexical-nesting lexical))
             (offset (lexical-offset lexical)))
        (etypecase lexical
          (env-lexical
           (eval-lambda (env)
             (environment-value env nesting offset)))))
      (if (globally-constant-p var)
          (eval-lambda (env)
            (declare (ignore env))
            (symbol-value var))
          (progn
            (assume-special context var)
            (eval-lambda (env)
              (declare (ignore env))
              (unless (boundp var)
                (error 'unbound-variable :name var))
              (symbol-value var))))))


(defun body-decls&forms (exprs)
  (let* ((decl-exprs
           (loop while (and (consp (first exprs))
                            (eq 'declare (first (first exprs))))
                 for expr = (pop exprs)
                 collect expr))
         (decls (reduce #'append (mapcar #'rest decl-exprs))))
    (values decls exprs)))

(defun decl-specials (declaration)
  (when (eq (first declaration) 'special)
    (rest declaration)))

(defmacro with-parsed-body ((forms-var specials-var) exprs &body body)
  (let ((decls (gensym)))
    `(multiple-value-bind (,decls ,forms-var) (body-decls&forms ,exprs)
       (let ((,specials-var (mapcan #'decl-specials ,decls)))
         ,@body))))


(declaim (ftype (function ((or symbol list) context) eval-closure) prepare-function-ref))
(defun prepare-function-ref (function-name context)
  (if (context-var-lexical-p context `(function ,function-name))
      (let* ((lexical (context-find-lexical context `(function ,function-name)))
             (nesting (lexical-nesting lexical))
             (offset  (lexical-offset lexical)))
        (eval-lambda (env)
          (environment-value env nesting offset)))
      (let ((f* (sb-c::fdefinition-object function-name t)))
        (eval-lambda (env)
          (declare (ignore env))
          (or (sb-c::fdefn-fun f*)
              (error 'undefined-function :name function-name))))))


(declaim (ftype (function (context (or symbol list)) *) context-find-function))
(defun context-find-function (context f)
  (context-find-lexical context `(function ,f)))

(declaim (ftype (function (context (or symbol list)) *) local-function-p))
(defun local-function-p (context f)
  (context-find-function context f))

(declaim (ftype (function () eval-closure) prepare-nil))
(defun prepare-nil ()
  (eval-lambda (env) (declare (ignore env))))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-local-call))
(defun prepare-local-call (f args context)
  (let* ((args* (mapcar (lambda (form) (prepare-form form context)) args))
         (flex (context-find-function context f))
         (offset (lexical-offset flex))
         (nesting (lexical-nesting flex)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (eval-lambda (env)
                 (funcall (the function (environment-value env nesting offset))
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var) env)))))))
        (eval-lambda (env)
          (apply (the function (environment-value env nesting offset))
                 (mapcar (lambda (x) (funcall (the eval-closure x) env)) args*))))))

(declaim (ftype (function ((or symbol list) list context) eval-closure) prepare-global-call))
(defun prepare-global-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args))
        (f* (sb-c::fdefinition-object f t)))
    (if (< (length args) 20)
        (specialize m% (length args) (loop for i from 0 below 20 collect i)
          (let ((argvars (loop for i from 0 below m%
                               collect (gensym (format nil "ARG~D-" i)))))
            `(let ,(loop for var in argvars
                         for i from 0 below m%
                         collect `(,var (nth ,i args*)))
               (eval-lambda (env)
                 (declare (ignorable env))
                 (funcall (or (sb-c::fdefn-fun f*)
                              (error 'undefined-function :name f))
                          ,@(loop for var in argvars
                                  collect `(funcall (the eval-closure ,var) env)))))))
        (eval-lambda (env)
          (apply (or (sb-c::fdefn-fun f*)
                     (error 'undefined-function :name f))
                 (mapcar (lambda (x) (funcall (the eval-closure x) env))
                         args*))))))

(declaim (ftype (function (eval-closure list context) eval-closure) prepare-direct-call))
(defun prepare-direct-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args)))
    (eval-lambda (env)
      (apply (the (or symbol function) (funcall (the eval-closure f) env))
             (mapcar (lambda (x) (funcall (the eval-closure x) env)) args*)))))

(declaim (ftype (function (list context &optional symbol)
                          (values eval-closure &rest nil))
                prepare-progn))
(defun prepare-progn (forms context &optional (*mode* *mode*))
  (let ((body* (mapcar (lambda (form) (prepare-form form context)) forms)))
    (if (null body*)
        (prepare-nil)
        (let ((forms* (butlast body*))
              (last-form* (first (last body*))))
          (eval-lambda (env)
            (dolist (form* forms*)
              (funcall (the eval-closure form*) env))
            (funcall (the eval-closure last-form*) env))))))

(defun lambda-binding-vars (entry kind)
  (check-type kind (member :aux :optional :key :required))
  (ecase kind
    ((:key :optional)
     (etypecase entry
       (cons   (list (etypecase (first entry)
                       (cons   (second (first entry)))
                       (symbol (first entry)))
                     (if (cddr entry)
                         (third entry)
                         (gensym))))
       (symbol (list entry (gensym)))))
    ((:required)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))
    ((:aux)
     (etypecase entry
       (cons   (list (first entry)))
       (symbol entry)))))

(defun lambda-binding-main-var (entry)
  (etypecase entry
    (cons   (etypecase (first entry)
              (cons   (second (first entry)))
              (symbol (first entry))))
    (symbol entry)))

(defun lambda-simple-binding-vars (entry)
  (etypecase entry
    (cons   (list (first entry)))
    (symbol (list entry))))

(defun lambda-binding-default (entry)
  (etypecase entry
    (cons   (second entry))
    (symbol nil)))

(defun lambda-key (entry)
  (flet ((keywordify (sym)
           (intern (symbol-name sym) "KEYWORD")))
    (etypecase entry
      (cons   (etypecase (first entry)
                (cons   (first (first entry)))
                (symbol (keywordify (first entry)))))
      (symbol (keywordify entry)))))

(declaim (ftype (function * eval-closure) prepare-macro-lambda))
(defun prepare-macro-lambda (name lambda-form context)
  (destructuring-bind (lambda-list &rest body)
      lambda-form
    (let* ((whole (gensym "WHOLE"))
           (env   (gensym "ENV"))
           (body-form (sb-kernel:parse-defmacro lambda-list
                                                whole
                                                body
                                                name
                                                'macrolet
                                                :environment env)))
      (prepare-lambda `((,whole ,env) ,body-form)
                      context
                      ;;:name name
                      ))))

(defmacro incff (x &optional (num 1))
  (let ((old-x (gensym)))
    `(let ((,old-x ,x))
       (incf ,x ,num)
       ,old-x)))

(defmacro nlet (loop-var bindings &body body)
  `(labels ((,loop-var ,(mapcar #'first bindings)
              ,@body))
     (,loop-var ,@(mapcar #'second bindings))))

(defmacro dnlet (loop-var bindings &body body)
  `(labels ((,loop-var ,(mapcar #'first bindings)
              ,@body))
     (declare (dynamic-extent #',loop-var))
     (,loop-var ,@(mapcar #'second bindings))))

(declaim (ftype (function * eval-closure) prepare-lambda))
(defun prepare-lambda (lambda-form context &key (name nil namep))
  (destructuring-bind (lambda-list &rest exprs) lambda-form
    (with-parsed-body (body specials) exprs
      (multiple-value-bind (required optional restp rest keyp keys allowp auxp aux
                            morep more-context more-count)
          (sb-int:parse-lambda-list lambda-list)
        (declare (ignore more-context more-count))
        (declare (ignorable auxp))
        (when morep
          (error "The interpreter does not support the lambda-list keyword ~S"
                 'sb-int:&more))
        (let* ((argvars (append required
                                (mapcan (lambda (x) (lambda-binding-vars x :optional)) optional)
                                (and restp (list rest))
                                (mapcan (lambda (x) (lambda-binding-vars x :key)) keys)
                                (mapcan (lambda (x) (lambda-binding-vars x :aux)) aux)))
               (keywords (mapcar #'lambda-key keys))
               (required-num (length required))
               (optional-num (length optional))
               (key-num (length keys))
               (aux-num (length aux))
               (default-values (append (mapcar #'lambda-binding-default optional)
                                       (mapcar #'lambda-binding-default keys)
                                       (mapcar #'lambda-binding-default aux)))
               (new-context (make-lexical-context context))
               (varspecs (list))
               (varnum 0)
               (default-values*
                 (flet ((register-var (var)
                          (if (or (member var specials :test #'eq)
                                  (globally-special-p var))
                              (progn
                                (context-add-special! new-context var)
                                (push (cons :special var) varspecs))
                              (progn
                                (context-add-env-lexical! new-context var)
                                (push :lexical varspecs)
                                (incf (the fixnum varnum))))))
                   (mapc #'register-var required)
                   (flet ((process-bindings (bindings kind)
                            (loop for binding in bindings
                                  for default-value = (lambda-binding-default binding)
                                  for vars = (lambda-binding-vars binding kind)
                                  collect (prepare-form default-value new-context)
                                  do (mapc #'register-var vars))))
                     (append (process-bindings optional :optional)
                             (progn (when restp (register-var rest)) '())
                             (process-bindings keys :key)
                             (process-bindings aux :aux)))))
               (envp (or (> varnum +stack-max+)
                         (maybe-closes-over-p context `(progn ,@body) argvars)
                         (some (lambda (x) (maybe-closes-over-p context x argvars))
                               default-values)))
               (body-context (context-add-specials new-context specials))
               (body* (prepare-form
                       (if namep
                           `(block ,(sb-int:fun-name-block-name name) ,@body)
                           `(progn ,@body))
                       body-context))
               (unbound (gensym)))
          (setq varspecs (nreverse varspecs))
          (flet
              ((handle-arguments (new-env &rest args)
                 (declare (dynamic-extent args))
                 ;; All this ELT and LENGTH stuff is not as
                 ;; inefficient as it looks.  SBCL transforms
                 ;; &rest into &more here.
                 (dnlet iter
                     ((rest
                       (when (or restp keyp)
                         (loop for i
                               from (+ required-num optional-num)
                               below (length args)
                               collect (elt args i))))
                      (restnum (max 0 (- (length args) (+ required-num optional-num))))
                      (keys-checked-p nil)
                      (my-default-values* default-values*)
                      (my-keywords keywords)
                      (my-varspecs varspecs)
                      (argi 0)        ;how many actual arguments have
                                      ;been processed
                      (vari 0)        ;how many lexical vars have been
                                      ;bound
                      (i 0))          ;how many formal arguments have
                                      ;been processed
                     (declare (fixnum restnum argi vari i))
                     (flet ((push-args (&rest values)
                              ;; Push VALUES onto the
                              ;; environment.
                              (incf i)
                              (dolist (value values)
                                (let ((varspec (pop my-varspecs)))
                                  (if (eq varspec :lexical)
                                      (setf
                                       (environment-value new-env 0 (incff vari))
                                       value)
                                      (let ((var (cdr varspec)))
                                        (assert (eq :special
                                                    (car varspec))
                                                (varspec))
                                        (return-from iter
                                          (progv (list var) (list value)
                                            (iter rest restnum keys-checked-p
                                                  my-default-values* my-keywords
                                                  my-varspecs argi vari i)))))))))
                       (declare (inline push-args))
                       (prog ()
                        positional
                          (when (>= argi (length args))
                            (go missing-optionals))
                          (when (>= argi (the fixnum
                                              (+ required-num optional-num)))
                            (go rest))
                          (if (>= argi required-num)
                              (progn
                                (pop my-default-values*)
                                (push-args (elt args (incff argi)) t))
                              (push-args (elt args (incff argi))))
                          (go positional)
                        missing-optionals
                          (unless (>= argi required-num)
                            (error 'sb-int:simple-program-error
                                   :format-control "invalid number of arguments: ~D (expected: >=~D)"
                                   :format-arguments (list (length args) required-num)))
                          (when (>= i (the fixnum (+ required-num
                                                     optional-num)))
                            (go rest))
                          (let ((val* (pop my-default-values*)))
                            (push-args (funcall (the eval-closure val*)
                                                new-env)
                                       nil))
                          (go missing-optionals)
                        rest
                          (when (>= i (the fixnum
                                           (+ (if restp 1 0)
                                              (the fixnum
                                                   (+ required-num optional-num)))))
                            (go keys))
                          (when restp
                            (push-args rest))
                        keys
                          (unless keyp
                            (unless (or restp (= argi (length args)))
                              (error 'sb-int:simple-program-error
                                     :format-control "invalid number of arguments: ~D (expected: <=~D)"
                                     :format-arguments (list (length args) (+ required-num optional-num))))
                            (go aux))
                          (unless (evenp restnum)
                            (error 'sb-int:simple-program-error
                                   :format-control "odd number of keyword arguments: ~S"
                                   :format-arguments (list rest)))
                          (when (>= i
                                    (the fixnum
                                         (+ (if restp 1 0)
                                            (the fixnum
                                                 (+ required-num
                                                    (the fixnum
                                                         (+ optional-num
                                                            key-num)))))))
                            (unless (or keys-checked-p
                                        allowp
                                        (getf rest :allow-other-keys nil))
                              (loop for (k v) on rest by #'cddr
                                    unless (or (eq k :allow-other-keys)
                                               (member k keywords :test #'eq))
                                    do (error 'sb-int:simple-program-error
                                              :format-control "unknown &KEY argument: ~A"
                                              :format-arguments (list k)))
                              (setq keys-checked-p t))
                            (go aux))
                          (let* ((key  (the symbol (pop my-keywords)))
                                 (val* (pop my-default-values*))
                                 (x    (getf rest key unbound)))
                            (if (eq unbound x)
                                (progn
                                  (push-args (funcall (the eval-closure val*) new-env)
                                             nil))
                                (progn
                                  (push-args x t))))
                          (go keys)
                        aux
                          (when (>= i
                                    (+ (if restp 1 0)
                                       (the fixnum
                                            (+ required-num
                                               (the fixnum
                                                    (+ optional-num
                                                       key-num))
                                               aux-num))))
                            (go final-call))
                          (let ((val* (pop my-default-values*)))
                            (push-args (funcall (the eval-closure val*)
                                                new-env)))
                          (go aux)
                        final-call
                          (assert (null my-default-values*)
                                  (my-default-values*))
                          (return
                            (funcall body* new-env)))))))
              ;;(declare (inline handle-arguments))  ;crashes the compiler! lp#1203260
              (if envp
                  (eval-lambda (env)
                    (lambda (&rest args)
                      (declare (dynamic-extent args))
                      (let ((new-env (make-environment env varnum)))
                        (apply #'handle-arguments new-env args))))
                  (eval-lambda (env)
                    (lambda (&rest args)
                      (declare (dynamic-extent args))
                      (with-dynamic-extent-environment (new-env env varnum)
                        (apply #'handle-arguments new-env args)))))))))))

(defun context->native-environment (context)
  (let ((functions
          (loop for (name . expander) in (context-collect context 'context-macros)
                collect `(,name . (sb-c::macro . ,expander))))
        (vars
          (loop for (name . form) in (context-collect context 'context-symbol-macros)
                collect `(,name . (sb-c::macro . ,form)))))
    (sb-c::internal-make-lexenv functions vars nil nil nil nil nil nil nil nil nil)))

(defun native-environment->context (lexenv)
  (with-accessors ((functions sb-c::lexenv-funs)
                   (vars      sb-c::lexenv-vars))
      lexenv
    (let ((context (make-context nil))
          (macros%
            (loop for (name . functional) in vars
                  when (eq (car functional) 'sb-c::macro)
                  collect `(,name . ,(cdr functional))))
          (symbol-macros%
            (loop for (name . form) in functions
                  when (eq (car form) 'sb-c::macro)
                  collect `(,name . ,(cdr form)))))
      (with-slots (macros symbol-macros)
          context
        (setq macros macros%)
        (setq symbol-macros symbol-macros%))
      context)))

(defun globally-special-p (var)
  (eq :special (sb-int:info :variable :kind var)))

(defun globally-constant-p (var)
  (eq :constant (sb-int:info :variable :kind var)))

(defun assume-special (context var)
  (unless (or (globally-special-p var)
              (context-var-special-p context var))
    (warn 'simple-warning
          :format-control "Undefined variable: ~S"
          :format-arguments (list var))))

(defun prevent-constant-modification (var)
  (when (globally-constant-p var)
    (warn "~S is a constant and thus can't be set." var)))

(declaim (ftype (function (* context &optional symbol) eval-closure) prepare-form))
(defun prepare-form (form context &optional (mode *mode*)
                                  &aux (*mode* :execute)
                                       (*form* form)
                                       (sb-c::*current-path*
                                        (when (boundp 'sb-c::*source-paths*)
                                          (sb-c::ensure-source-path form))))
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  ;;(print form)
  (values
   (cond
     ((sb-int:self-evaluating-p form)
      (eval-lambda (env) (declare (ignore env)) form))
     (t
      (etypecase form
        (symbol
         (let ((macro? (context-find-symbol-macro context form)))
           (if macro?
               (prepare-form macro? context mode)
               (prepare-ref form context))))
        (cons
         (case (first form)
           ((if)
            (destructuring-bind (a b &optional c) (rest form)
              (let ((a* (prepare-form a context))
                    (b* (prepare-form b context))
                    (c* (prepare-form c context)))
                (eval-lambda (env) (if (funcall a* env) (funcall b* env) (funcall c* env))))))
           ((function)
            (let ((fun-form (second form)))
              (etypecase fun-form
                (symbol
                 (prepare-function-ref fun-form context))
                (cons
                 (case (first fun-form)
                   ((lambda)
                    (prepare-lambda (rest fun-form) context))
                   ((sb-int:named-lambda)
                    (prepare-lambda (cddr fun-form) context))
                   (t
                    (assert (sb-int:valid-function-name-p fun-form))
                    (prepare-function-ref fun-form context)))))))
           ((lambda)
            (prepare-lambda (rest form) context))
           ((setq)
            (let ((binding-forms (rest form)))
              (let ((bindings
                      (loop for (var valform) on binding-forms by #'cddr
                            collect var
                            collect
                               (cond ((context-var-symbol-macro-p context var)
                                      (let ((form
                                              (context-find-symbol-macro context var)))
                                        (prepare-form `(setf ,form ,valform)
                                                      context)))
                                     ((context-var-lexical-p context var)
                                      (context-find-lexical context var))
                                     (t
                                      (assume-special context var)
                                      (prevent-constant-modification var)
                                      :special))
                            collect (prepare-form valform context))))
                (eval-lambda (env)
                  (loop for (var info val*) on bindings by #'cdddr
                        for value = (funcall (the eval-closure val*) env)
                        for result =
                           (etypecase info
                             (function ;symbol macro setter
                              (funcall info env))
                             (lexical
                              (setf (environment-value env
                                                       (lexical-nesting info)
                                                       (lexical-offset info))
                                    value))
                             (keyword
                              (setf (symbol-value var) value)))
                        finally (return result))))))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((tag* (prepare-form tag context))
                    (body* (prepare-progn body context)))
                (eval-lambda (env)
                  (catch (funcall tag* env)
                    (funcall body* env))))))
           ((block)
            (destructuring-bind (name &body body) (rest form)
              (let* ((tag (gensym (concatenate 'string "BLOCK-" (symbol-name name))))
                     (body* (prepare-progn body (context-add-block-tag context name tag))))
                (eval-lambda (env)
                  (catch tag
                    (funcall body* env))))))
           ((declare)
            (warn "DECLARE in form context.")
            (prepare-nil))
           ((eval-when)
            (destructuring-bind ((&rest times) &body body) (rest form)
              (cond ((member mode '(:not-compile-time :compile-time-too))
                     (let ((ct (or (member :compile-toplevel times)
                                   (member 'cl:compile times)))
                           (lt (or (member :load-toplevel times)
                                   (member 'cl:load times)))
                           (e  (or (member :execute times)
                                   (member 'cl:eval times))))
                       (cond ((and lt ct)
                              (prepare-progn body context :compile-time-too))
                             ((and lt e)
                              (prepare-progn body context mode))
                             (lt
                              (prepare-progn body context :not-compile-time))
                             (ct
                              (prepare-progn body context))
                             ((and e (eq mode :compile-time-too))
                              (prepare-progn body context))
                             (t
                              (prepare-nil)))))
                    ((or (member :execute times)
                         (member 'cl:eval times))
                     (prepare-progn body context))
                    (t
                     (prepare-nil)))))
           ((flet)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((bindings* (mapcar (lambda (form)
                                            (if (listp form)
                                                (cons (first form)
                                                      (prepare-lambda (rest form)
                                                                      context
                                                                      :name (first form)))
                                                (cons form (prepare-nil))))
                                          bindings))
                       (new-context
                         (context-add-env-functions context (mapcar #'first bindings*)))
                       (functions (mapcar #'cdr bindings*))
                       (n (length functions))
                       (body* (prepare-progn body
                                             (context-add-specials new-context
                                                                   specials))))
                  (eval-lambda (env)
                    (let ((new-env (make-environment env n)))
                      (loop for i from 0 to n
                            for f in functions
                            do (setf (environment-value new-env 0 i)
                                     (funcall (the eval-closure f) env)))
                      (funcall body* new-env)))))))
           ((labels)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((new-context (context-add-env-functions context (mapcar #'first bindings)))
                       (bindings* (mapcar (lambda (form)
                                            (if (listp form)
                                                (cons (first form)
                                                      (prepare-lambda (rest form) new-context :name (first form)))
                                                (cons form (prepare-nil))))
                                          bindings))
                       (functions (mapcar #'cdr bindings*))
                       (n (length functions))
                       (body* (prepare-progn body (context-add-specials new-context
                                                                        specials))))
                  (eval-lambda (env)
                    (let ((new-env (make-environment env n)))
                      (loop for i from 0 to n
                            for f in functions
                            do (setf (environment-value new-env 0 i)
                                     (funcall (the eval-closure f) new-env)))
                      (funcall body* new-env)))))))
           ((let)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((real-bindings (mapcar (lambda (form)
                                                (if (listp form)
                                                    (cons (first form) (second form))
                                                    (cons form nil)))
                                              bindings))
                       (vars (mapcar #'car real-bindings))
                       (varnum (length vars))
                       (envp (or (> varnum +stack-max+)
                                 (maybe-closes-over-p context `(progn ,@body) vars)))
                       (new-context
                         (context-add-env-lexicals context (list)))
                       srav-laiceps)
                  (let* ((values*
                           (loop for (var . value-form) in real-bindings
                                 for val* = (prepare-form value-form context)
                                 if (or (member (the symbol var) specials)
                                        (globally-special-p var))
                                 collect (cons t   val*)
                                 and do (push var srav-laiceps)
                                        (context-add-special! new-context var)
                                 else
                                 collect (cons nil val*)
                                 and do (context-add-env-lexical! new-context var)))
                         (body* (prepare-progn body
                                               (context-add-specials
                                                new-context
                                                specials))))
                    (if envp
                        (eval-lambda (env)
                          (let ((new-env (make-environment env varnum))
                                (slav-laiceps (list)))
                            (loop with i fixnum = 0
                                  for (specialp . val*) in values*
                                  when specialp
                                  do (push (funcall (the eval-closure val*) env)
                                           slav-laiceps)
                                  else
                                  do (setf (environment-value new-env 0 i)
                                           (funcall (the eval-closure val*) env))
                                     (incf i))
                            (progv
                                srav-laiceps
                                slav-laiceps
                              (funcall body* new-env))))
                        (eval-lambda (env)
                          (with-dynamic-extent-environment (new-env env varnum)
                            (let ((slav-laiceps (list)))
                              (loop with i fixnum = 0
                                    for (specialp . val*) in values*
                                    when specialp
                                    do (push (funcall (the eval-closure val*) env)
                                             slav-laiceps)
                                    else
                                    do (setf (environment-value new-env 0 i)
                                             (funcall (the eval-closure val*) env))
                                       (incf i))
                              (progv
                                  srav-laiceps
                                  slav-laiceps
                                (funcall body* new-env)))))))))))
           ((let*)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (labels ((build-nested-let (bindings)
                           (if (null bindings)
                               `(progn ,@body)
                               (let* ((binding-form (first bindings))
                                      (var (if (listp binding-form) (first binding-form) binding-form))
                                      (val (if (listp binding-form) (second binding-form) nil)))
                                 `(let ((,var ,val))
                                    (declare (special
                                              ,@(if (or (member var specials)
                                                        (globally-special-p var))
                                                    (list var)
                                                    nil)))
                                    ,(build-nested-let (rest bindings)))))))
                  (prepare-form (build-nested-let bindings) context)))))
           ((load-time-value)
            (let ((load-form (cadr form)))
              ;; FIXME
              (prepare-form load-form context)))
           ((locally)
            (destructuring-bind (&rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let ((new-context (context-add-specials context specials)))
                  (prepare-progn body new-context)))))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f context))
                    (argforms* (mapcar (lambda (x) (prepare-form x context)) argforms)))
                (eval-lambda (env)
                  (apply (funcall (the eval-closure f*) env)
                         (mapcan (lambda (arg)
                                   (multiple-value-list
                                    (funcall (the eval-closure arg) env)))
                                 argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form context))
                    (body*        (prepare-progn body context)))
                (eval-lambda (env)
                  (multiple-value-prog1
                      (funcall values-form* env)
                    (funcall body* env))))))
           ((multiple-value-setq)
            (destructuring-bind (vars values-form) (rest form)
              (if vars
                  (prepare-form `(values (setf (values ,@vars) ,values-form)) context)
                  (prepare-form `(values ,values-form) context))))
           ((multiple-value-bind)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (vars value-form &body exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let* ((value-form*  (prepare-form value-form context))
                       (varspecs     (loop for var in vars
                                           collect (if (or (member var specials)
                                                           (globally-special-p var))
                                                       (cons :special var)
                                                       :lexical)))
                       (lexicals     (loop for var in vars
                                           for spec in varspecs
                                           when (eq spec :lexical)
                                           collect var))
                       (our-specials (loop for var in vars
                                           for spec in varspecs
                                           unless (eq spec :lexical)
                                           collect var))
                       (nlexicals    (list-length lexicals))
                       (new-context  (context-add-specials
                                      (context-add-env-lexicals context lexicals)
                                      specials))
                       (body*        (prepare-progn body new-context)))
                  (eval-lambda (env)
                    (let* ((new-env (make-environment env nlexicals))
                           (values  (multiple-value-list (funcall value-form* env))))
                      (progv our-specials '()
                        (loop with i = 0
                              for spec in varspecs
                              when (eq spec :lexical)
                                do (setf (environment-value new-env 0 i) (pop values))
                                   (incf i)
                              else
                                do (setf (symbol-value (cdr spec)) (pop values)))
                        (funcall body* new-env))))))))
           ((progn)
            (prepare-progn (rest form) context mode))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals context))
                    (vars* (prepare-form vars context))
                    (body* (prepare-progn body context)))
                (eval-lambda (env)
                  (progv (funcall vals* env) (funcall vars* env)
                    (funcall body* env))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (eval-lambda (env)
                (declare (ignore env))
                quoted-object)))
           ((return-from)
            (destructuring-bind (name &optional value) (rest form)
              (let ((value* (prepare-form value context))
                    (tag    (context-block-tag context name)))
                (eval-lambda (env)
                  (throw tag (funcall value* env))))))
           ((the)
            (prepare-form (third form) context))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag    context))
                    (result* (prepare-form result context)))
                (eval-lambda (env)
                  (throw (funcall tag* env) (funcall result* env))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected context))
                    (body*      (prepare-progn body      context)))
                (eval-lambda (env)
                  (unwind-protect (funcall protected* env)
                    (funcall body* env))))))
           ((sb-ext:truly-the)
            (prepare-form (third form) context))
           ((sb-int:named-lambda)
            (prepare-lambda (cddr form) context))
           ((symbol-macrolet)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let ((bindings (mapcar (lambda (form)
                                          (destructuring-bind (var macro-form) form
                                            (when (or (globally-special-p var)
                                                      (member var specials))
                                              (error 'sb-int:simple-program-error
                                                     :format-control "Attempt to bind a special variable with SYMBOL-MACROLET: ~S"
                                                     :format-arguments (list var)))
                                            (when (constantp var)
                                              (error 'sb-int:simple-program-error
                                                     :format-control "Attempt to bind a special variable with SYMBOL-MACROLET: ~S"
                                                     :format-arguments (list var)))
                                            (cons var macro-form)))
                                        bindings)))
                  (prepare-progn body
                                 (context-add-specials
                                  (context-add-symbol-macros context bindings)
                                  specials)
                                 mode)))))
           ((macrolet)
            (destructuring-bind (bindings &rest exprs) (rest form)
              (with-parsed-body (body specials) exprs
                (let ((bindings (mapcar (lambda (form)
                                          (cons (first form)
                                                (funcall
                                                 (prepare-macro-lambda (first form)
                                                                       (rest form)
                                                                       context)
                                                 (make-null-environment))))
                                        bindings)))
                  (prepare-progn body
                                 (context-add-specials
                                  (context-add-macros context bindings)
                                  specials)
                                 mode)))))
           ((go)
            (let* ((go-tag    (second form))
                   (catch-tag (context-find-go-tag context go-tag)))
              (eval-lambda (env)
                (declare (ignore env))
                (throw catch-tag go-tag))))
           ((tagbody)
            ;; 1. set up catch handler
            ;; 2. save go-tag -> tagbody-catch-tag mapping
            (let* ((jump (gensym "JUMP"))
                   (tags-and-bodies (parse-tagbody-tags-and-bodies (rest form)))
                   (new-context (context-add-go-tags context (mapcar #'car tags-and-bodies) jump))
                   (tags-and-bodies* (mapcar (lambda (x)
                                               (destructuring-bind (tag . body) x
                                                 (cons tag (prepare-progn body new-context))))
                                             tags-and-bodies)))
              (eval-lambda (env)
                (block tagbody-loop
                  (let ((code tags-and-bodies*))
                    (loop
                      (setq code
                            (member (catch jump
                                      (dolist (tag-and-body* code)
                                        (funcall (the eval-closure (cdr tag-and-body*))
                                                 env))
                                      (return-from tagbody-loop))
                                    tags-and-bodies*
                                    :key #'car))
                      (unless code
                        (return-from tagbody-loop)))))
                nil)))
           (otherwise
            ;; FIXME: Handle SETF expanders?
            (destructuring-bind (f . args) form
              (check-type f (or list symbol))
              (let ((local-macro? (context-find-macro context f))
                    (global-macro? (and (symbolp f) (macro-function f))))
                (cond
                  (local-macro?
                   (let ((macro-function local-macro?))
                     (prepare-form (funcall (the function macro-function)
                                            form
                                            (context->native-environment context))
                                   context)))
                  ((local-function-p context f)
                   (prepare-local-call f args context))
                  (global-macro?
                   (prepare-form (funcall global-macro? form (context->native-environment context)) context))
                  ((and (listp f)
                        (eq 'lambda (first f)))
                   (let ((lambda-fn (prepare-lambda (rest f) context)))
                     (prepare-direct-call lambda-fn args context)))
                  (t
                   (prepare-global-call f args context)))))))))))
   t))

(defun eval (form)
  (funcall (prepare-form form (make-null-context) :execute)
           (make-null-environment)))

(defun eval-tlf (form)
  (funcall (prepare-form form (make-null-context) :not-compile-time)
           (make-null-environment)))

(defun load (filename)
  ;;FIXME: set :LOAD-TOPLEVEL time.
  (let ((eof (gensym)))
    (with-open-file (in filename)
      (loop for form = (read in nil eof nil)
            until (eq form eof)
            do (eval-tlf form)))))

(defun install ()
  (sb-ext:without-package-locks
    (defun sb-impl::eval-in-lexenv (exp lexenv)
      (ccase sb-ext:*evaluator-mode*
        #+(or)
        ((:interpret)
         (sb-impl::simple-eval-in-lexenv exp lexenv))
        ((:interpret)
         (funcall (sb-eval2::prepare-form exp
                                          (sb-eval2::native-environment->context lexenv)
                                          (if sb-impl::*eval-tlf-index*
                                              :not-compile-time
                                              :execute))
                  (sb-eval2::make-null-environment)))
        ((:compile)
         (sb-eval:eval-in-native-environment exp lexenv))))))

;; * enable with:
;;
;; (sb-eval2:install)
;; (setq sb-ext:*evaluator-mode* :interpret)

#+(or)
(funcall (prepare-form '(funcall
                         (funcall
                          (lambda (x)
                            (lambda (y z)
                              (setq x (+ x (* y z)))
                              x))
                          3)
                         5 7)
                       (make-null-context))
         (make-null-environment))

#+(or)
(funcall (funcall
          (prepare-form
           '(lambda (a b &optional c (d 10 dp) &rest r &key e (f 12 fp) (g 12 gp) &aux (h 1) (i 2))
             (list a b c d dp e f fp g gp r h i)))
          (make-null-environment))
         1 2 3 4 :f 5 :e 6)
;; => (1 2 3 4 T 6 5 T 12 NIL (:F 5 :E 6) 1 2)
