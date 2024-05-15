#lang racket
(require syntax/location)
(require (for-syntax syntax/location))

(define-syntax-rule (dbg body)
  (let ([res body])
    (eprintf "[~a:~a] ~v = ~a~%"
      (syntax-source-file-name #'body)
      (syntax-line #'body)
      'body
      res)
    res))

(define-syntax-rule (err msg)
  (error 'error
    (format "[~a:~a] ~a"
      (syntax-source-file-name #'msg)
      (syntax-line #'msg)
      msg)))

(define-syntax-rule (note msg)
  (eprintf "~a~%" msg))

(define-syntax (todo stx)
  (with-syntax ([src (syntax-source-file-name stx)] [line (syntax-line stx)])
    #'(error 'todo (format "[~a:~a] unimplemented" src line))))

; todo: write a trace macro
; todo: write a fmt alias to format
; todo: write a namer

(provide dbg err note todo)
; todo: how to provide everything??
