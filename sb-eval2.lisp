(defpackage "SB-EVAL2"
  (:use "COMMON-LISP"))

(in-package "SB-EVAL2")

#+(or)
(setq SB-EXT:*EVALUATOR-MODE* :interpret)

(defvar *lexicals* nil)

(defstruct lexical type offset)
(defstruct ref value)

(defstruct (environment (:constructor %make-environment))
  variables
  functions)
(defun make-null-environment ()
  (%make-environment :variables nil :functions nil))
(defun make-environment (parent-environment)
  (with-slots (variables functions)
      parent-environment
    (%make-environment :variables variables :functions functions)))

(defstruct (context (:constructor %make-context))
  block-tags
  go-tags
  symbol-macros
  macros)
(defun make-null-context ()
  (%make-context :block-tags nil))
(defun make-context (parent-context)
  (with-slots (block-tags)
      parent-context
    (%make-context :block-tags block-tags)))
(defun context-add-block-tag (context block tag)
  (let ((new-context (make-context context)))
    (with-slots (block-tags)
        new-context
      (setq block-tags (acons block tag block-tags)))
    new-context))
(defun context-block-tag (context block)
  (let ((tag (cdr (assoc block (context-block-tags context)))))
    (assert tag)
    tag))
(defun context-add-go-tags (context new-go-tags catch-tag)
  (let ((new-context (make-context context)))
    (with-slots (go-tags)
        new-context
      (dolist (new-go-tag new-go-tags)
        (setq go-tags (acons new-go-tag catch-tag go-tags))))
    new-context))
(defun context-find-go-tag (context go-tag)
  (cdr (assoc go-tag (context-go-tags context))))
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
             (let ((tag next-form)
                   (forms (loop until (symbolp (setq next-form (pop forms)))
                                collect next-form)))
               (unless forms
                 (setq finishp t))
               (cons tag forms)))))

(defun prepare-ref (var context)
  (declare (ignore context))
  (lambda (env) (cdr (assoc var (environment-variables env) :test #'eq))))

(defun prepare-function-ref (f context)
  (declare (ignore context))
  (lambda (env)
    (let ((local-function-record (assoc f (environment-functions env) :test #'equal)))
      (if local-function-record
          (cdr local-function-record)
          ;; Global functions can be called through their function names.
          f))))

(defun prepare-nil ()
  (lambda (env) (declare (ignore env))))

(defun prepare-function-call (f args context)
  (let ((args* (mapcar (lambda (form) (prepare-form form context)) args)))
    (lambda (env)
      (apply (funcall f env)
             (mapcar (lambda (x) (funcall x env)) args*)))))

(defun prepare-progn (forms context)
  (let ((body* (mapcar (lambda (form) (prepare-form form context)) forms)))
    (lambda (env)
      (let (result)
        (dolist (form* body* result)
          (setq result (funcall form* env)))))))

(defun prepare-lambda (lambda-form context)
  (destructuring-bind (lambda-list &rest body) lambda-form
    ;; FIXME: SPECIAL declarations!
    (let ((body* (prepare-progn body context)))
      (lambda (env)
        (lambda (&rest args)
          ;; FIXME: non-simple lambda-lists
          (let ((new-env (make-environment env)))
            (loop for val in args
                  for var in lambda-list
                  do (push `(,var . ,val) (environment-variables new-env)))
            (funcall body* new-env)))))))

(defun context->native-environment (context)
  ;;FIXME
  context)

(defun prepare-form (form &optional (context (make-null-context)))
  ;;(declare (optimize speed (safety 0) (space 1) (debug 0)))
  ;;(print form)
  (values
   (cond
     ((sb-int:self-evaluating-p form)
      (lambda (env) (declare (ignore env)) form))
     (t
      (etypecase form
        (symbol
         (let ((macro? (assoc form (context-symbol-macros context))))
                (if macro?
                    (funcall (cdr macro?))
                    (prepare-ref form context))))
        (cons
         (case (first form)
           ((if)
            (destructuring-bind (a b c) (rest form)
              (let ((a* (prepare-form a context))
                    (b* (prepare-form b context))
                    (c* (prepare-form c context)))
                (lambda (env) (if (funcall a* env) (funcall b* env) (funcall c* env))))))
           ((function)
            (let ((fun-form (second form)))
              (etypecase fun-form
                (symbol
                 (prepare-function-ref fun-form context))
                (cons
                 (ecase (first fun-form)
                   ((lambda)
                    (prepare-lambda (rest fun-form) context))
                   ((setf
                     (prepare-function-ref fun-form context))))))))
           ((lambda)
            (prepare-lambda (rest form) context))
           ((setq)
            (let ((binding-forms (rest form)))
              (let ((bindings
                      (loop for (var valform) on binding-forms by #'cddr
                            collect var
                            collect (prepare-form valform context))))               
                (lambda (env)
                  (loop with env-vars = (environment-variables env)
                        for (var val*) on bindings by #'cddr
                        for result = (setf (cdr (assoc var env-vars)) (funcall val* env))
                        finally (return result))))))
           ((catch)
            (destructuring-bind (tag &body body) (rest form)
              (let ((k (prepare-progn body context)))
                (lambda (env)
                  (catch tag
                    (funcall k env))))))
           ((block)
            (destructuring-bind (name &body body) (rest form)
              (let* ((tag (gensym (concatenate 'string "BLOCK-" (symbol-name name))))
                     (body* (prepare-progn body (context-add-block-tag context name tag))))
                (lambda (env)
                  (catch tag
                    (funcall body* env))))))
           ((declare)
            ;;FIXME
            (lambda (env) (declare (ignore env)) nil))
           ((eval-when)
            (destructuring-bind ((&rest times) &body body) (rest form)
              (if (or (member :load-toplevel times)
                      (member :execute times)
                      (member 'load times)
                      (member 'eval times))
                  (prepare-progn body context)
                  (prepare-nil))))
           ((flet)
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((body* (prepare-progn body context))
                    (bindings* (mapcar (lambda (form)
                                         (if (listp form)
                                             (cons (first form)
                                                   (prepare-lambda (rest form) context))
                                             (cons form (prepare-nil))))
                                       bindings)))
                (lambda (env)
                  (let ((new-env (make-environment env)))
                    (loop for (var . val) in bindings*
                          do (push `(,var . ,(funcall val env))
                                   (environment-functions new-env)))
                    (funcall body* new-env))))))
           ((labels)
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((body* (prepare-progn body context))
                    (bindings* (mapcar (lambda (form)
                                         (if (listp form)
                                             (cons (first form)
                                                   (prepare-lambda (rest form) context))
                                             (cons form (prepare-nil))))
                                       bindings)))
                (lambda (env)
                  (let ((new-env (make-environment env)))
                    (loop for (var . val) in bindings*
                          do (push `(,var . ,(funcall val new-env))
                                   (environment-functions new-env)))
                    (funcall body* new-env))))))
           ((let)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((body* (prepare-progn body context))
                    (bindings* (mapcar (lambda (form)
                                         (if (listp form)
                                             (cons (first form)
                                                   (prepare-form (second form) context))
                                             (cons form (prepare-nil))))
                                       bindings)))
                (lambda (env)
                  (let ((new-env (make-environment env)))
                    (loop for (var . val) in bindings*
                          do (push `(,var . ,(funcall val env))
                                   (environment-variables new-env)))
                    (funcall body* new-env))))))
           ((let*)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (bindings &rest body) (rest form)
              (labels ((prepare-let* (bindings context)
                         (if (endp bindings)
                             (prepare-progn body context)
                             (destructuring-bind (binding . rest-bindings) bindings
                               (let* ((var  (if (listp binding) (first binding) binding))
                                      (val  (if (listp binding) (prepare-form (second binding) context) (prepare-nil)))
                                      (new-context context)
                                      (more (prepare-let* rest-bindings new-context)))
                                 (lambda (env)
                                   (let ((new-env (make-environment env)))
                                     (push `(,var . ,val) (environment-variables new-env))
                                     (funcall more new-env))))))))
                (prepare-let* bindings context))))
           ((locally))
           ((multiple-value-call)
            (destructuring-bind (f &rest argforms) (rest form)
              (let ((f* (prepare-form f context))
                    (argforms* (mapcar (lambda (x) (prepare-form x context)) argforms)))
                (lambda (env)
                  (apply f* (mapcan (lambda (arg) (multiple-value-list (funcall arg env))) argforms*))))))
           ((multiple-value-prog1)
            (destructuring-bind (values-form &body body) (rest form)
              (let ((values-form* (prepare-form values-form context))
                    (body*        (prepare-progn body context)))
                (lambda (env)
                  (multiple-value-prog1
                      (funcall values-form* env)
                    (funcall body*))))))
           ((multiple-value-setq)
            (destructuring-bind (vars values-form) (rest form)
              (let ((values-form* (prepare-form values-form context)))
                (lambda (env)
                  (let* ((values        (multiple-value-list (funcall values-form* env)))
                         (primary-value (first values))
                         (env-vars      (environment-variables env)))
                    (dolist (var vars)
                      (setf (cdr (assoc var env-vars)) (pop values)))
                    primary-value)))))
           ((multiple-value-bind)
            ;; FIXME: SPECIAL declarations!
            (destructuring-bind (vars value-form &body body) (rest form)
              (let ((value-form* (prepare-form value-form context))
                    (body*       (prepare-progn body context)))
                (lambda (env)
                  (let* ((new-env (make-environment env))
                         (values  (multiple-value-list (funcall value-form* env))))
                    (dolist (var vars)
                      (push `(,var . ,(pop values)) (environment-variables new-env)))
                    (funcall body* new-env))))))
           ((progn)
            (prepare-progn (rest form) context))
           ((progv)
            (destructuring-bind (vals vars &body body) (rest form)
              (let ((vals* (prepare-form vals context))
                    (vars* (prepare-form vars context))
                    (body* (prepare-progn body context)))
                (lambda (env)
                  (progv (funcall vals* env) (funcall vars* env)
                    (funcall body* env))))))
           ((quote)
            (let ((quoted-object (cadr form)))
              (lambda (env)
                (declare (ignore env))
                quoted-object)))
           ((return-from)
            (destructuring-bind (name &optional value) (rest form)
              (let ((value* (prepare-form value context))
                    (tag    (context-block-tag context name)))
                (lambda (env)
                  (throw tag (funcall value* env))))))
           ((the)
            (prepare-form (third form) context))
           ((throw)
            (destructuring-bind (tag result) (rest form)
              (let ((tag*    (prepare-form tag    context))
                    (result* (prepare-form result context)))
                (lambda (env)
                  (throw (funcall tag* env) (funcall result* env))))))
           ((unwind-protect)
            (destructuring-bind (protected &body body) (rest form)
              (let ((protected* (prepare-form  protected context))
                    (body*      (prepare-progn body      context)))
                (lambda (env)
                  (unwind-protect (funcall protected* env)
                    (funcall body* env))))))
           ((sb-ext:truly-the)
            (prepare-form (third form) context))
           ((sb-int:named-lambda)
            (prepare-lambda (rest form) context))
           ((symbol-macrolet)
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((bindings (mapcar (lambda (form)
                                        (cons (first form) (second form)))
                                      bindings)))
                (prepare-progn body (context-add-symbol-macros context bindings)))))
           ((macrolet)
            ;; FIXME: This doesn't actually work because we disregard
            ;; the lambda list when calling the macro.
            (destructuring-bind (bindings &rest body) (rest form)
              (let ((bindings (mapcar (lambda (form)
                                        (cons (first form)
                                              (funcall
                                               (prepare-lambda (rest form) context)
                                               (make-null-environment))))
                                      bindings)))
                (prepare-progn body (context-add-macros context bindings)))))
           ((go)
            (let* ((go-tag    (second form))
                   (catch-tag (context-find-go-tag context go-tag)))
              (lambda (env)
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
              (lambda (env)
                (block tagbody-loop
                  (let ((code tags-and-bodies*))
                    (loop
                      (setq code
                            (member (catch jump
                                      (dolist (tag-and-body* code)
                                        (funcall (cdr tag-and-body*) env))
                                      (return-from tagbody-loop))
                                    tags-and-bodies*
                                    :key #'car))
                      (unless code
                        (return-from tagbody-loop)))))
                nil)))
           (otherwise
            ;; FIXME: Handle SETF expanders?
            (destructuring-bind (f . args) form
              (let ((local-macro? (assoc f (context-macros context)))
                    (global-macro? (macro-function f)))
                (cond
                  (local-macro?
                   (let ((macro-function (cdr local-macro?)))
                     (prepare-form (funcall macro-function form (context->native-environment context)) context)))
                  (global-macro?
                   (prepare-form (funcall global-macro? form (context->native-environment context)) context))
                  ((and (listp f)
                        (listp (first f))
                        (eq 'lambda (first (first f))))
                   (let ((lambda-fn (prepare-lambda (rest (first f)) context)))
                     (prepare-function-call lambda-fn args context)))
                  (t
                   (prepare-function-call (prepare-function-ref f context) args context)))))))))))
   t))


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
