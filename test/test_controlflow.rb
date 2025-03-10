require 'minitest/autorun'
$LOAD_PATH << File.dirname(__FILE__) + '/../lib'
require 'rdl'
require 'octokit'
require 'types/core'
require 'tempfile'

# RDL Global Info ; hashtable -> have a graph key
# # %{
# predicate #{pred_name}(v:Variables, v':Variables) 
#     requires Valid(v)
# {
#     && v.state == #{initial_state}
#     && v'.state == Done
#     && v'.read == v.read
#     && v'.write == v.write - 1
#     && v'.success == v.success + 1
#     && v'.success <= 1
# }
# }
# 
# To Do: Multiple resbody, path sensitive effects (Rescue shows effects of both branches)

class TestControlFlow < Minitest::Test
  extend RDL::Annotate

  type :dummy, '() -> Integer [open or close or write]', typecheck: :controlflow
  def dummy
    begin
      f = File.open('test')
      1+1
    rescue IOError => e
      # a = 1+1
      # b = f.close rescue retry
      # if f == nil
      #   retry
      # end
      retry
    end
  end

  type Octokit::Client, :create_issue, '(String, String, String) -> Sawyer::Resource [Write<Issue>]'
  type Octokit::Client, :list_issues, '(String) -> Array<Sawyer::Resource> [Read<Issue>]'
  type Sawyer::Resource, :title, '() -> String'

  type :create_issue,'(Octokit::Client, String, Integer) -> Sawyer::Resource [Write<Issue>]', typecheck: :later
  def create_issue(octokit, username, attempts)
    response = octokit.create_issue("#{username}/test-repo2", 'Test Issue 1', 'This is a test issue')
    raise "Simulated error" if attempts == 0  
    response
  end

  type :safe_create_issue, '(Octokit::Client, String, Integer) -> Sawyer::Resource [Read<Issue> or Write<Issue>]', typecheck: :later
  def safe_create_issue(octokit, username, attempts)
      begin
          puts create_issue(octokit, username, attempts)
      rescue => e
          attempts += 1
          if attempts < 3
              issues = octokit.list_issues("#{username}/test-repo2") rescue retry
              if issues.any? { |issue| issue.title == 'Test Issue 1' }
                  puts "An error occurred: #{e.message}. Issue already exists. No more retries."
              else
                  puts "#{attempts} An error occurred: #{e.message}. Retrying..."
                  retry
              end
          else
              puts "An error occurred: #{e.message}. No more retries."
          end
      end
  end

  def test_controlflow
    # RDL.do_typecheck :controlflow
    RDL.do_typecheck :later
  end
end