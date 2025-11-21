package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.*;

/**
 * Test class for AggiungiLibroRepartoServlet
 * Tests the functionality of displaying available books to add to a department (Reparto)
 */
class AggiungiLibroRepartoServletTest {

    private AggiungiLibroRepartoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private RepartoDAO repartoDAO;
    private LibroDAO libroDAO;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiLibroRepartoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        repartoDAO = mock(RepartoDAO.class);
        libroDAO = mock(LibroDAO.class);
    }

    /**
     * Test successful retrieval with books available and none already in reparto
     * Expected: All books in the list, forward to stampaLibri.jsp
     */
    @Test
    void testDoGet_SuccessfulRetrievalWithAvailableBooks() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(1);
        reparto.setNome("Narrativa");
        reparto.setDescrizione("Libri di narrativa");

        Libro libro1 = new Libro();
        libro1.setIsbn("123-456");
        libro1.setTitolo("Libro 1");

        Libro libro2 = new Libro();
        libro2.setIsbn("789-012");
        libro2.setTitolo("Libro 2");

        List<Libro> allLibri = new ArrayList<>();
        allLibri.add(libro1);
        allLibri.add(libro2);

        when(repartoDAO.doRetrieveById(1)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(allLibri);
        when(repartoDAO.getAppartenenza(1)).thenReturn(Collections.emptyList());
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto);
        verify(request).setAttribute(eq("libri"), argThat(list -> 
            list instanceof List && ((List<?>) list).size() == 2
        ));
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when some books are already in the reparto (covers the filtering branch)
     * Expected: Only books not in reparto are shown
     */
    @Test
    void testDoGet_FiltersBooksAlreadyInReparto() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("2");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(2);
        reparto.setNome("Saggistica");

        Libro libro1 = new Libro();
        libro1.setIsbn("111-111");
        libro1.setTitolo("Libro Già Presente");

        Libro libro2 = new Libro();
        libro2.setIsbn("222-222");
        libro2.setTitolo("Libro Disponibile");

        Libro libro3 = new Libro();
        libro3.setIsbn("333-333");
        libro3.setTitolo("Altro Libro Disponibile");

        List<Libro> allLibri = new ArrayList<>();
        allLibri.add(libro1);
        allLibri.add(libro2);
        allLibri.add(libro3);

        List<Libro> libriGiaPresenti = new ArrayList<>();
        libriGiaPresenti.add(libro1);

        when(repartoDAO.doRetrieveById(2)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(allLibri);
        when(repartoDAO.getAppartenenza(2)).thenReturn(libriGiaPresenti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto);
        verify(request).setAttribute(eq("libri"), argThat(list -> {
            if (!(list instanceof List)) return false;
            List<?> libroList = (List<?>) list;
            return libroList.size() == 2 && 
                   !libroList.contains(libro1) &&
                   libroList.contains(libro2) &&
                   libroList.contains(libro3);
        }));
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when all books are already in the reparto
     * Expected: Empty list of available books
     */
    @Test
    void testDoGet_AllBooksAlreadyInReparto() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("3");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(3);
        reparto.setNome("Storia");

        Libro libro1 = new Libro();
        libro1.setIsbn("AAA-111");

        Libro libro2 = new Libro();
        libro2.setIsbn("BBB-222");

        List<Libro> allLibri = new ArrayList<>();
        allLibri.add(libro1);
        allLibri.add(libro2);

        List<Libro> libriGiaPresenti = new ArrayList<>();
        libriGiaPresenti.add(libro1);
        libriGiaPresenti.add(libro2);

        when(repartoDAO.doRetrieveById(3)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(allLibri);
        when(repartoDAO.getAppartenenza(3)).thenReturn(libriGiaPresenti);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto);
        verify(request).setAttribute(eq("libri"), argThat(list -> 
            list instanceof List && ((List<?>) list).isEmpty()
        ));
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when no books exist in the system
     * Expected: Empty list of available books
     */
    @Test
    void testDoGet_NoBooksinSystem() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("4");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(4);
        reparto.setNome("Fumetti");

        when(repartoDAO.doRetrieveById(4)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(Collections.emptyList());
        when(repartoDAO.getAppartenenza(4)).thenReturn(Collections.emptyList());
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto);
        verify(request).setAttribute(eq("libri"), argThat(list -> 
            list instanceof List && ((List<?>) list).isEmpty()
        ));
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test with null idReparto parameter
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_NullIdReparto_ThrowsException() throws Exception {
        when(request.getParameter("idReparto")).thenReturn(null);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        assertThrows(NumberFormatException.class, () -> {
            servlet.doGet(request, response);
        });

        verify(repartoDAO, never()).doRetrieveById(anyInt());
        verify(dispatcher, never()).forward(request, response);
    }

    /**
     * Test with invalid idReparto parameter (not a number)
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_InvalidIdReparto_ThrowsException() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("invalid");

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        assertThrows(NumberFormatException.class, () -> {
            servlet.doGet(request, response);
        });

        verify(repartoDAO, never()).doRetrieveById(anyInt());
        verify(dispatcher, never()).forward(request, response);
    }

    /**
     * Test when getAppartenenza returns null (documents bug in servlet)
     * Expected: NullPointerException when checking isEmpty()
     */
    @Test
    void testDoGet_GetAppartenenzaReturnsNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("5");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(5);

        List<Libro> allLibri = new ArrayList<>();
        Libro libro1 = new Libro();
        libro1.setIsbn("TEST-123");
        allLibri.add(libro1);

        when(repartoDAO.doRetrieveById(5)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(allLibri);
        when(repartoDAO.getAppartenenza(5)).thenReturn(null);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        assertThrows(NullPointerException.class, () -> {
            servlet.doGet(request, response);
        });
    }

    /**
     * Test dependency injection works correctly
     * Expected: Uses injected DAOs instead of creating new ones
     */
    @Test
    void testDoGet_UsesDependencyInjection() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("20");

        Reparto reparto = new Reparto();
        reparto.setIdReparto(20);

        when(repartoDAO.doRetrieveById(20)).thenReturn(reparto);
        when(libroDAO.doRetriveAll()).thenReturn(Collections.emptyList());
        when(repartoDAO.getAppartenenza(20)).thenReturn(Collections.emptyList());
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);
        servlet.setLibroDAO(libroDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).doRetrieveById(20);
        verify(libroDAO).doRetriveAll();
        verify(repartoDAO).getAppartenenza(20);
        verify(dispatcher).forward(request, response);
    }
}
