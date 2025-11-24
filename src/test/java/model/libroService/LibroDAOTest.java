package model.libroService;

import model.ConPool;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class LibroDAOTest {

    @Test
    public void testDoRetrieveById_found() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true);
        when(rs.getString(1)).thenReturn("ISBN1");
        when(rs.getString(2)).thenReturn("Titolo");
        when(rs.getString(3)).thenReturn("Genere");
        when(rs.getString(4)).thenReturn("2020");
        when(rs.getDouble(5)).thenReturn(12.5);
        when(rs.getInt(6)).thenReturn(10);
        when(rs.getString(7)).thenReturn("Trama");
        when(rs.getString(8)).thenReturn("img.png");
        when(rs.getBoolean(9)).thenReturn(true);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO spyDao = spy(new LibroDAO());
            Autore a = new Autore();
            a.setCf("CF1");
            List<Autore> authors = new ArrayList<>();
            authors.add(a);
            doReturn(authors).when(spyDao).getScrittura("ISBN1");

            Libro result = spyDao.doRetrieveById("ISBN1");

            assertNotNull(result);
            assertEquals("ISBN1", result.getIsbn());
            assertEquals("Titolo", result.getTitolo());
            assertEquals(12.5, result.getPrezzo());
            assertEquals(1, result.getAutori().size());
        }
    }

    @Test
    public void testSearch_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, true, false);
        when(rs.getString(1)).thenReturn("ISBN1", "ISBN2");
        when(rs.getString(2)).thenReturn("T1", "T2");
        when(rs.getString(3)).thenReturn("G1", "G2");
        when(rs.getString(4)).thenReturn("2020", "2021");
        when(rs.getDouble(5)).thenReturn(10.0, 20.0);
        when(rs.getInt(6)).thenReturn(0, 5);
        when(rs.getString(7)).thenReturn("tr1", "tr2");
        when(rs.getString(8)).thenReturn("i1.png", "i2.png");
        when(rs.getBoolean(9)).thenReturn(true, false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO spyDao = spy(new LibroDAO());
            doReturn(Collections.emptyList()).when(spyDao).getScrittura(anyString());

            List<Libro> list = spyDao.Search("query");

            assertNotNull(list);
            assertEquals(2, list.size());
            assertEquals("ISBN1", list.get(0).getIsbn());
            assertEquals("ISBN2", list.get(1).getIsbn());
        }
    }

    @Test
    public void testAddAutore_insertsAndSavesNewAutore() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Autore newAut = new Autore();
            newAut.setCf("CFA");

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> {
                        when(mock.searchAutore("CFA")).thenReturn(null);
                    })) {

                LibroDAO dao = new LibroDAO();
                dao.addAutore("ISBNX", newAut);

                // verify Scrittura insert executed
                verify(ps).setString(1, "CFA");
                verify(ps).setString(2, "ISBNX");
                verify(ps).executeUpdate();

                AutoreDAO constructed = mocked.constructed().get(0);
                verify(constructed).doSave(newAut);
            }
        }
    }

    @Test
    public void testDoRetrieveById_notFound_returnsNull() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            Libro l = dao.doRetrieveById("NOISBN");

            assertNull(l);
        }
    }

    @Test
    public void testDoRetriveAll_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement psAll = mock(PreparedStatement.class);
        PreparedStatement psScr = mock(PreparedStatement.class);
        ResultSet rsAll = mock(ResultSet.class);
        ResultSet rsScr = mock(ResultSet.class);

        when(conn.prepareStatement(contains("SELECT * FROM Libro"))).thenReturn(psAll);
        when(conn.prepareStatement(contains("FROM Scrittura"))).thenReturn(psScr);

        when(psAll.executeQuery()).thenReturn(rsAll);
        when(rsAll.next()).thenReturn(true, false);
        when(rsAll.getString(1)).thenReturn("ISBNA");
        when(rsAll.getString(2)).thenReturn("TitA");
        when(rsAll.getString(3)).thenReturn("G");
        when(rsAll.getString(4)).thenReturn("2019");
        when(rsAll.getDouble(5)).thenReturn(7.5);
        when(rsAll.getInt(6)).thenReturn(0);
        when(rsAll.getString(7)).thenReturn("tr");
        when(rsAll.getString(8)).thenReturn("img");
        when(rsAll.getBoolean(9)).thenReturn(true);

        when(psScr.executeQuery()).thenReturn(rsScr);
        when(rsScr.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            List<Libro> list = dao.doRetriveAll();

            assertNotNull(list);
            assertEquals(1, list.size());
            assertEquals("ISBNA", list.get(0).getIsbn());
        }
    }

    @Test
    public void testDeleteAutoreScrittura_deletesAndCallsDeleteAutore() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("DELETE FROM Scrittura"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> doNothing().when(mock).deleteAutore("CFAUT"))) {

                LibroDAO dao = new LibroDAO();
                Autore a = new Autore();
                a.setCf("CFAUT");

                dao.deleteAutoreScrittura("ISBNDEL", a);

                verify(ps).setString(1, "ISBNDEL");
                verify(ps).setString(2, "CFAUT");
                verify(ps).executeUpdate();

                AutoreDAO constructed = mocked.constructed().get(0);
                verify(constructed).deleteAutore("CFAUT");
            }
        }
    }

    @Test
    public void testAddAutore_whenAuthorExists_doesNotCallDoSave() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> when(mock.searchAutore("CFA")).thenReturn(new Autore()))) {

                LibroDAO dao = new LibroDAO();
                Autore a = new Autore();
                a.setCf("CFA");
                dao.addAutore("ISBN_EXIST", a);

                AutoreDAO constructed = mocked.constructed().get(0);
                verify(constructed, never()).doSave(any(Autore.class));
                verify(ps).executeUpdate();
            }
        }
    }

    @Test
    public void testUpdateLibroSconto_throwsWhenNoRowsUpdated() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Libro SET sconto"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            Libro l = new Libro();
            l.setIsbn("ISBNUP");
            l.setSconto(15);

            assertThrows(RuntimeException.class, () -> dao.updateLibroSconto(l));
        }
    }

    @Test
    public void testDeleteLibro_firstDeleteFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteLibro("ISBN_DEL_FAIL"));
        }
    }

    @Test
    public void testDoSave_callsAddAutore() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("NEWISBN");
            l.setTitolo("T");
            l.setGenere("G");
            l.setAnnoPubblicazioni("2025");
            l.setPrezzo(9.9);
            l.setSconto(0);
            l.setTrama("tr");
            l.setImmagine("img");

            Autore a = new Autore();
            a.setCf("CFA");
            List<Autore> aut = new ArrayList<>();
            aut.add(a);
            l.setAutori(aut);

            LibroDAO spyDao = spy(new LibroDAO());
            doNothing().when(spyDao).addAutore(eq("NEWISBN"), any(Autore.class));

            spyDao.doSave(l);

            verify(ps).setString(1, "NEWISBN");
            verify(ps).executeUpdate();
            verify(spyDao).addAutore(eq("NEWISBN"), any(Autore.class));
        }
    }

    @Test
    public void testDeleteLibro_lastDeleteFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteLibro("LASTFAIL"));
        }
    }

    @Test
    public void testUpdateLibro_throwsWhenNoRowsUpdated() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("ISBNUP");
            l.setTitolo("T");
            l.setGenere("G");
            l.setAnnoPubblicazioni("2020");
            l.setPrezzo(5.0);
            l.setSconto(1);
            l.setTrama("tr");
            l.setImmagine("img");

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.updateLibro(l));
        }
    }

    @Test
    public void testUpdateDisponibile_throwsWhenNoRowsUpdated() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("ISBNAV");
            l.setDisponibile(true);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.updateDisponibile(l));
        }
    }

    @Test
    public void testGetAppartenenzaReparto_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Appartenenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getInt(1)).thenReturn(3);

        Reparto reparto = new Reparto();
        reparto.setIdReparto(3);
        reparto.setDescrizione("desc");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<RepartoDAO> mocked = mockConstruction(RepartoDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById(3)).thenReturn(reparto))) {

                LibroDAO dao = new LibroDAO();
                List<Reparto> list = dao.getAppartenenzaReparto("ISBNR");

                assertNotNull(list);
                assertEquals(1, list.size());
                assertEquals(reparto, list.get(0));
            }
        }
    }

    @Test
    public void testGetPresenzaSede_returnsList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Presenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getInt(1)).thenReturn(7);

        Sede s = new Sede();
        s.setIdSede(7);
        s.setCitta("C");
        s.setVia("V");
        s.setCivico(1);
        s.setCap("00001");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<SedeDAO> mocked = mockConstruction(SedeDAO.class,
                    (mock, ctx) -> when(mock.doRetrieveById(7)).thenReturn(s))) {

                LibroDAO dao = new LibroDAO();
                List<Sede> list = dao.getPresenzaSede("ISBNS");

                assertNotNull(list);
                assertEquals(1, list.size());
                assertEquals(s, list.get(0));
            }
        }
    }

    @Test
    public void testDeleteAutoreScrittura_executeUpdate0_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("DELETE FROM Scrittura"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> doNothing().when(mock).deleteAutore("CFA"))) {

                LibroDAO dao = new LibroDAO();
                Autore a = new Autore();
                a.setCf("CFA");

                assertThrows(RuntimeException.class, () -> dao.deleteAutoreScrittura("ISBNX", a));
            }
        }
    }

    @Test
    public void testDoSave_throwsWhenInsertFails() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Libro"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("BAD");
            l.setTitolo("T");
            l.setGenere("G");
            l.setAnnoPubblicazioni("2025");
            l.setPrezzo(1.0);
            l.setSconto(0);
            l.setTrama("tr");
            l.setImmagine("img");
            l.setAutori(new ArrayList<>());

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.doSave(l));
        }
    }

    @Test
    public void testAddAutore_insertFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("INSERT INTO Scrittura"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(0);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> when(mock.searchAutore("CFX")).thenReturn(new Autore()))) {

                LibroDAO dao = new LibroDAO();
                Autore a = new Autore();
                a.setCf("CFX");
                assertThrows(RuntimeException.class, () -> dao.addAutore("ISBNX", a));
            }
        }
    }

    @Test
    public void testGetScrittura_returnsNullInListWhenAuthorMissing() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("SELECT cf FROM Scrittura"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getString(1)).thenReturn("CFNULL");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> when(mock.searchAutore("CFNULL")).thenReturn(null))) {

                LibroDAO dao = new LibroDAO();
                List<Autore> list = dao.getScrittura("ISBNZ");

                assertNotNull(list);
                assertEquals(1, list.size());
                assertNull(list.get(0));
            }
        }
    }

    @Test
    public void testDeleteLibro_middleDeleteFails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(0); // fail at third delete
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteLibro("MIDFAIL"));
        }
    }

    @Test
    public void testDeleteLibro_delete4Fails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(0); // fail at fourth delete (Sede)
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteLibro("DEL4"));
        }
    }

    @Test
    public void testDeleteLibro_delete5Fails_throws() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(0); // fail at fifth delete (Scrittura)
        when(ps6.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            assertThrows(RuntimeException.class, () -> dao.deleteLibro("DEL5"));
        }
    }

    @Test
    public void testUpdateLibro_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Libro SET"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("U1");
            l.setTitolo("T");
            l.setGenere("G");
            l.setAnnoPubblicazioni("2025");
            l.setPrezzo(4.5);
            l.setSconto(2);
            l.setTrama("tr");
            l.setImmagine("img");

            LibroDAO dao = new LibroDAO();
            dao.updateLibro(l);

            verify(ps).setString(1, "T");
            verify(ps).setString(8, "U1");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testUpdateDisponibile_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Libro SET disponibile"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("U2");
            l.setDisponibile(true);

            LibroDAO dao = new LibroDAO();
            dao.updateDisponibile(l);

            verify(ps).setBoolean(1, true);
            verify(ps).setString(2, "U2");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testUpdateLibroSconto_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);

        when(conn.prepareStatement(contains("UPDATE Libro SET sconto"))).thenReturn(ps);
        when(ps.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            Libro l = new Libro();
            l.setIsbn("S1");
            l.setSconto(20);

            LibroDAO dao = new LibroDAO();
            dao.updateLibroSconto(l);

            verify(ps).setInt(1, 20);
            verify(ps).setString(2, "S1");
            verify(ps).executeUpdate();
        }
    }

    @Test
    public void testDeleteLibro_success() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps1 = mock(PreparedStatement.class);
        PreparedStatement ps2 = mock(PreparedStatement.class);
        PreparedStatement ps3 = mock(PreparedStatement.class);
        PreparedStatement ps4 = mock(PreparedStatement.class);
        PreparedStatement ps5 = mock(PreparedStatement.class);
        PreparedStatement ps6 = mock(PreparedStatement.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps1, ps2, ps3, ps4, ps5, ps6);
        when(ps1.executeUpdate()).thenReturn(1);
        when(ps2.executeUpdate()).thenReturn(1);
        when(ps3.executeUpdate()).thenReturn(1);
        when(ps4.executeUpdate()).thenReturn(1);
        when(ps5.executeUpdate()).thenReturn(1);
        when(ps6.executeUpdate()).thenReturn(1);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            // should not throw
            dao.deleteLibro("GOODISBN");

            verify(ps6).setString(1, "GOODISBN");
            verify(ps6).executeUpdate();
        }
    }

    @Test
    public void testGetScrittura_returnsAuthorWhenPresent() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("SELECT cf FROM Scrittura"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(true, false);
        when(rs.getString(1)).thenReturn("CFAUTH");

        Autore a = new Autore();
        a.setCf("CFAUTH");
        a.setNome("N");

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            try (MockedConstruction<AutoreDAO> mocked = mockConstruction(AutoreDAO.class,
                    (mock, ctx) -> when(mock.searchAutore("CFAUTH")).thenReturn(a))) {

                LibroDAO dao = new LibroDAO();
                List<Autore> list = dao.getScrittura("ISBNX");

                assertNotNull(list);
                assertEquals(1, list.size());
                assertEquals(a, list.get(0));
            }
        }
    }

    @Test
    public void testSearch_empty_returnsEmptyList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(anyString())).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            List<Libro> list = dao.Search("nope");

            assertNotNull(list);
            assertTrue(list.isEmpty());
        }
    }

    @Test
    public void testGetAppartenenzaReparto_empty_returnsEmptyList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Appartenenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            List<Reparto> list = dao.getAppartenenzaReparto("ISBNNONE");

            assertNotNull(list);
            assertTrue(list.isEmpty());
        }
    }

    @Test
    public void testGetPresenzaSede_empty_returnsEmptyList() throws Exception {
        Connection conn = mock(Connection.class);
        PreparedStatement ps = mock(PreparedStatement.class);
        ResultSet rs = mock(ResultSet.class);

        when(conn.prepareStatement(contains("Presenza"))).thenReturn(ps);
        when(ps.executeQuery()).thenReturn(rs);
        when(rs.next()).thenReturn(false);

        try (MockedStatic<ConPool> cp = Mockito.mockStatic(ConPool.class)) {
            cp.when(ConPool::getConnection).thenReturn(conn);

            LibroDAO dao = new LibroDAO();
            List<Sede> list = dao.getPresenzaSede("ISBNNONE");

            assertNotNull(list);
            assertTrue(list.isEmpty());
        }
    }

}
