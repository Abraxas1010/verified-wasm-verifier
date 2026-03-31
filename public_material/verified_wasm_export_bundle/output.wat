(module
  (memory (export "memory") 1)
  (func $sky_reducer_step (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (param i32) (result i32) (local i32) (local i32) (local i32) (local i32) (local i32) (local i32) (local i32) (local i32)
    i32.const 0
    local.set 10
    i32.const 0
    local.set 11
    i32.const 0
    local.set 12
    i32.const 0
    local.set 13
    i32.const 0
    local.set 14
    i32.const 0
    local.set 15
    i32.const 0
    local.set 16
    i32.const 0
    local.set 17
    local.get 6
    i32.load offset=0
    local.set 11
    local.get 7
    i32.load offset=0
    local.set 12
    local.get 8
    i32.load offset=0
    local.set 13
    local.get 11
    local.get 13
    i32.lt_s
    if
      local.get 0
      local.get 11
      i32.const 4
      i32.mul
      i32.add
      i32.load offset=0
      local.set 10
      local.get 10
      i32.const 0
      i32.eq
      if
        local.get 2
        local.get 11
        i32.const 4
        i32.mul
        i32.add
        i32.load offset=0
        local.set 14
        local.get 5
        local.get 12
        i32.add
        local.get 14
        i32.store offset=0
        local.get 1
        local.get 11
        i32.const 4
        i32.mul
        i32.add
        i32.load offset=0
        local.set 11
        local.get 12
        i32.const 1
        i32.add
        local.set 12
        local.get 6
        local.get 11
        i32.store offset=0
        local.get 7
        local.get 12
        i32.store offset=0
        local.get 8
        local.get 13
        i32.store offset=0
        i32.const 1
        return
      else
        local.get 10
        i32.const 1
        i32.eq
        if
          local.get 12
          i32.const 2
          i32.ge_s
          if
            local.get 5
            local.get 12
            i32.const 1
            i32.sub
            i32.const 4
            i32.mul
            i32.add
            i32.load offset=0
            local.set 14
            local.get 14
            local.set 11
            local.get 12
            i32.const 2
            i32.sub
            local.set 12
            local.get 6
            local.get 11
            i32.store offset=0
            local.get 7
            local.get 12
            i32.store offset=0
            local.get 8
            local.get 13
            i32.store offset=0
            i32.const 1
            return
          else
            local.get 6
            local.get 11
            i32.store offset=0
            local.get 7
            local.get 12
            i32.store offset=0
            local.get 8
            local.get 13
            i32.store offset=0
            i32.const 0
            return
          end
        else
          local.get 10
          i32.const 2
          i32.eq
          if
            local.get 12
            i32.const 3
            i32.ge_s
            if
              local.get 13
              i32.const 3
              i32.add
              local.get 9
              i32.le_s
              if
                local.get 5
                local.get 12
                i32.const 1
                i32.sub
                i32.const 4
                i32.mul
                i32.add
                i32.load offset=0
                local.set 14
                local.get 5
                local.get 12
                i32.const 2
                i32.sub
                i32.const 4
                i32.mul
                i32.add
                i32.load offset=0
                local.set 15
                local.get 5
                local.get 12
                i32.const 3
                i32.sub
                i32.const 4
                i32.mul
                i32.add
                i32.load offset=0
                local.set 16
                local.get 0
                local.get 13
                i32.const 0
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 1
                local.get 13
                i32.const 0
                i32.add
                i32.add
                local.get 14
                i32.store offset=0
                local.get 2
                local.get 13
                i32.const 0
                i32.add
                i32.add
                local.get 16
                i32.store offset=0
                local.get 3
                local.get 13
                i32.const 0
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 0
                local.get 13
                i32.const 1
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 1
                local.get 13
                i32.const 1
                i32.add
                i32.add
                local.get 15
                i32.store offset=0
                local.get 2
                local.get 13
                i32.const 1
                i32.add
                i32.add
                local.get 16
                i32.store offset=0
                local.get 3
                local.get 13
                i32.const 1
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 0
                local.get 13
                i32.const 2
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 1
                local.get 13
                i32.const 2
                i32.add
                i32.add
                local.get 13
                i32.const 0
                i32.add
                i32.store offset=0
                local.get 2
                local.get 13
                i32.const 2
                i32.add
                i32.add
                local.get 13
                i32.const 1
                i32.add
                i32.store offset=0
                local.get 3
                local.get 13
                i32.const 2
                i32.add
                i32.add
                i32.const 0
                i32.store offset=0
                local.get 13
                i32.const 2
                i32.add
                local.set 11
                local.get 13
                i32.const 3
                i32.add
                local.set 13
                local.get 12
                i32.const 3
                i32.sub
                local.set 12
                local.get 6
                local.get 11
                i32.store offset=0
                local.get 7
                local.get 12
                i32.store offset=0
                local.get 8
                local.get 13
                i32.store offset=0
                i32.const 1
                return
              else
                local.get 6
                local.get 11
                i32.store offset=0
                local.get 7
                local.get 12
                i32.store offset=0
                local.get 8
                local.get 13
                i32.store offset=0
                i32.const 2
                return
              end
            else
              local.get 6
              local.get 11
              i32.store offset=0
              local.get 7
              local.get 12
              i32.store offset=0
              local.get 8
              local.get 13
              i32.store offset=0
              i32.const 0
              return
            end
          else
            local.get 10
            i32.const 3
            i32.eq
            if
              local.get 12
              i32.const 1
              i32.ge_s
              if
                local.get 13
                i32.const 2
                i32.add
                local.get 9
                i32.le_s
                if
                  local.get 5
                  local.get 12
                  i32.const 1
                  i32.sub
                  i32.const 4
                  i32.mul
                  i32.add
                  i32.load offset=0
                  local.set 14
                  local.get 0
                  local.get 13
                  i32.const 0
                  i32.add
                  i32.add
                  i32.const 0
                  i32.store offset=0
                  local.get 1
                  local.get 13
                  i32.const 0
                  i32.add
                  i32.add
                  local.get 11
                  i32.store offset=0
                  local.get 2
                  local.get 13
                  i32.const 0
                  i32.add
                  i32.add
                  local.get 14
                  i32.store offset=0
                  local.get 3
                  local.get 13
                  i32.const 0
                  i32.add
                  i32.add
                  i32.const 0
                  i32.store offset=0
                  local.get 0
                  local.get 13
                  i32.const 1
                  i32.add
                  i32.add
                  i32.const 0
                  i32.store offset=0
                  local.get 1
                  local.get 13
                  i32.const 1
                  i32.add
                  i32.add
                  local.get 14
                  i32.store offset=0
                  local.get 2
                  local.get 13
                  i32.const 1
                  i32.add
                  i32.add
                  local.get 13
                  i32.const 0
                  i32.add
                  i32.store offset=0
                  local.get 3
                  local.get 13
                  i32.const 1
                  i32.add
                  i32.add
                  i32.const 0
                  i32.store offset=0
                  local.get 13
                  i32.const 1
                  i32.add
                  local.set 11
                  local.get 13
                  i32.const 2
                  i32.add
                  local.set 13
                  local.get 12
                  i32.const 1
                  i32.sub
                  local.set 12
                  local.get 6
                  local.get 11
                  i32.store offset=0
                  local.get 7
                  local.get 12
                  i32.store offset=0
                  local.get 8
                  local.get 13
                  i32.store offset=0
                  i32.const 1
                  return
                else
                  local.get 6
                  local.get 11
                  i32.store offset=0
                  local.get 7
                  local.get 12
                  i32.store offset=0
                  local.get 8
                  local.get 13
                  i32.store offset=0
                  i32.const 2
                  return
                end
              else
                local.get 6
                local.get 11
                i32.store offset=0
                local.get 7
                local.get 12
                i32.store offset=0
                local.get 8
                local.get 13
                i32.store offset=0
                i32.const 0
                return
              end
            else
              local.get 10
              i32.const 4
              i32.eq
              if
                local.get 12
                i32.const 2
                i32.ge_s
                if
                  local.get 5
                  local.get 12
                  i32.const 1
                  i32.sub
                  i32.const 4
                  i32.mul
                  i32.add
                  i32.load offset=0
                  local.set 14
                  local.get 5
                  local.get 12
                  i32.const 2
                  i32.sub
                  i32.const 4
                  i32.mul
                  i32.add
                  i32.load offset=0
                  local.set 15
                  local.get 3
                  local.get 11
                  i32.const 4
                  i32.mul
                  i32.add
                  i32.load offset=0
                  local.set 17
                  local.get 4
                  local.get 17
                  i32.const 4
                  i32.mul
                  i32.add
                  i32.load offset=0
                  i32.const 0
                  i32.ne
                  if
                    local.get 14
                    local.set 11
                    local.get 12
                    i32.const 2
                    i32.sub
                    local.set 12
                    local.get 6
                    local.get 11
                    i32.store offset=0
                    local.get 7
                    local.get 12
                    i32.store offset=0
                    local.get 8
                    local.get 13
                    i32.store offset=0
                    i32.const 1
                    return
                  else
                    local.get 15
                    local.set 11
                    local.get 12
                    i32.const 2
                    i32.sub
                    local.set 12
                    local.get 6
                    local.get 11
                    i32.store offset=0
                    local.get 7
                    local.get 12
                    i32.store offset=0
                    local.get 8
                    local.get 13
                    i32.store offset=0
                    i32.const 1
                    return
                  end
                else
                  local.get 6
                  local.get 11
                  i32.store offset=0
                  local.get 7
                  local.get 12
                  i32.store offset=0
                  local.get 8
                  local.get 13
                  i32.store offset=0
                  i32.const 0
                  return
                end
              else
                local.get 6
                local.get 11
                i32.store offset=0
                local.get 7
                local.get 12
                i32.store offset=0
                local.get 8
                local.get 13
                i32.store offset=0
                i32.const 0
                return
              end
            end
          end
        end
      end
    else
      local.get 6
      local.get 11
      i32.store offset=0
      local.get 7
      local.get 12
      i32.store offset=0
      local.get 8
      local.get 13
      i32.store offset=0
      i32.const 0
      return
    end
    unreachable
  )
  (export "sky_reducer_step" (func 0))
)
