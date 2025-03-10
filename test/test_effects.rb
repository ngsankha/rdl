require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'types/core'
require 'tempfile'

class TestEffects < Minitest::Test
  extend RDL::Annotate

  type :pure_method, '(Integer) -> Integer [.]', typecheck: :effects
  def pure_method(x)
    x
  end

  type :do_io, '() -> %any [open or write or close]', typecheck: :effects
  def do_io
    f = File.open('test')
    f.write("hello world")
    f.close
  end

  type :test_rescue, '() -> %any [open or close]', typecheck: :effects
  def test_rescue
    begin
      raise "error"
    rescue
      f = File.open('test')
      f.close
    end
  end

  type :test_if, '() -> %any [open or write or close]', typecheck: :effects
  def test_if
    if true
      f = File.open('test')
    else
      puts "no file"
      do_io()
    end
  end

  type :foo, '() -> %any [open]', typecheck: :effects
  def foo
    f = File.open('test')
  end

  type :test_functioncall, '() -> %any [open]', typecheck: :effects
  def test_functioncall
    foo()
  end

  def test_effects
    RDL.do_typecheck :effects
  end
end
