package tchdl.util

sealed trait Report
sealed trait Error extends Report
sealed trait Warning extends Report
sealed trait Info extends Report


