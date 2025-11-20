package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

/**
 * Unit tests for AggiungiLibroSedeServlet
 * Tests the servlet's ability to add books to a store location (sede) by displaying
 * available books, filtering out already present books, and forwarding to the view.
 */
class AggiungiLibroSedeServletTest {

    private AggiungiLibroSedeServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new AggiungiLibroSedeServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    /**
     * Test successful retrieval of available books for a sede
     * Scenario: Sede exists, books are available, none are already present
     */
    @Test
    void testDoGet_SuccessfulBookRetrieval() throws IOException, ServletException {
        // Arrange: Set valid sede ID
        when(request.getParameter("idSede")).thenReturn("1");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        // Create test data
        Sede sede = new Sede();
        sede.setIdSede(1);
        sede.setCitta("Milano");

        List<Libro> allBooks = createMockBooks(3);
        List<Libro> presentBooks = new ArrayList<>();

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(1)).thenReturn(sede);
            when(mock.getPresenza(1)).thenReturn(presentBooks);
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(allBooks);
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Verify sede and books are set as attributes
            verify(request).setAttribute("sede", sede);
            verify(request).setAttribute("libri", allBooks);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test book filtering when some books are already present in sede
     * Scenario: Sede has 2 books already present, 5 total books available
     * Expected: Only 3 books should be available for addition
     */
    @Test
    void testDoGet_FiltersOutAlreadyPresentBooks() throws IOException, ServletException {
        // Arrange: Set valid sede ID
        when(request.getParameter("idSede")).thenReturn("2");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(2);
        sede.setCitta("Roma");

        // Create 5 total books
        List<Libro> allBooks = createMockBooks(5);

        // Create list of 2 books already present
        List<Libro> presentBooks = new ArrayList<>();
        presentBooks.add(allBooks.get(0));
        presentBooks.add(allBooks.get(1));

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(2)).thenReturn(sede);
            when(mock.getPresenza(2)).thenReturn(presentBooks);
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>(allBooks));
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Verify that only 3 books remain after filtering
            verify(request).setAttribute(eq("libri"), any(List.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test when sede has no books present yet
     * Scenario: All books should be available for addition to this sede
     */
    @Test
    void testDoGet_NoBooksPresentInSede() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("3");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(3);
        sede.setCitta("Torino");

        List<Libro> allBooks = createMockBooks(4);
        List<Libro> presentBooks = new ArrayList<>();

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(3)).thenReturn(sede);
            when(mock.getPresenza(3)).thenReturn(presentBooks);
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(allBooks);
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: All books should be available
            verify(request).setAttribute("libri", allBooks);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test when all books are already present in sede
     * Scenario: Sede has all available books, empty list should be returned
     */
    @Test
    void testDoGet_AllBooksAlreadyPresentInSede() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("4");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(4);
        sede.setCitta("Bologna");

        List<Libro> allBooks = createMockBooks(2);
        List<Libro> presentBooks = new ArrayList<>(allBooks);

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(4)).thenReturn(sede);
            when(mock.getPresenza(4)).thenReturn(presentBooks);
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>(allBooks));
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Empty list should be provided after filtering
            verify(request).setAttribute(eq("libri"), any(List.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test correct request dispatcher forwarding
     * Scenario: Request should be forwarded to the correct JSP page
     */
    @Test
    void testDoGet_CorrectDispatcherPath() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("5");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(5);

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(5)).thenReturn(sede);
            when(mock.getPresenza(5)).thenReturn(new ArrayList<>());
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>());
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Verify correct dispatcher path is used
            verify(request).getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp");
        }
    }

    /**
     * Test with empty book catalog
     * Scenario: No books available in system
     */
    @Test
    void testDoGet_EmptyBookCatalog() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("6");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(6);

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(6)).thenReturn(sede);
            when(mock.getPresenza(6)).thenReturn(new ArrayList<>());
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>());
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Empty list should be returned
            verify(request).setAttribute("libri", new ArrayList<>());
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test sede attribute is correctly set
     * Scenario: Verify sede object is properly retrieved and set
     */
    @Test
    void testDoGet_SedeAttributeSet() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("7");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede expectedSede = new Sede();
        expectedSede.setIdSede(7);
        expectedSede.setCitta("Napoli");
        expectedSede.setVia("Via Marina");
        expectedSede.setCivico(15);
        expectedSede.setCap("80100");

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(7)).thenReturn(expectedSede);
            when(mock.getPresenza(7)).thenReturn(new ArrayList<>());
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>());
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact sede object is set
            verify(request).setAttribute("sede", expectedSede);
        }
    }

    /**
     * Test large number of books
     * Scenario: Sede has many books available
     */
    @Test
    void testDoGet_LargeNumberOfBooks() throws IOException, ServletException {
        // Arrange
        when(request.getParameter("idSede")).thenReturn("8");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp")).thenReturn(dispatcher);

        Sede sede = new Sede();
        sede.setIdSede(8);

        List<Libro> allBooks = createMockBooks(100);
        List<Libro> presentBooks = new ArrayList<>();
        for (int i = 0; i < 20; i++) {
            presentBooks.add(allBooks.get(i));
        }

        try (MockedConstruction<SedeDAO> sedeDAOMocked = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrieveById(8)).thenReturn(sede);
            when(mock.getPresenza(8)).thenReturn(presentBooks);
        });
             MockedConstruction<LibroDAO> libroDAOMocked = mockConstruction(LibroDAO.class, (mock, context) -> {
                 when(mock.doRetriveAll()).thenReturn(new ArrayList<>(allBooks));
             })) {

            // Act
            servlet.doGet(request, response);

            // Assert: Proper handling of large list
            verify(request).setAttribute(eq("libri"), any(List.class));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Helper method to create mock books
     *
     * @param count Number of mock books to create
     * @return List of mock books with unique ISBNs and titles
     */
    private List<Libro> createMockBooks(int count) {
        List<Libro> books = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            Libro libro = new Libro();
            libro.setIsbn("ISBN-" + i);
            libro.setTitolo("Libro " + i);
            libro.setGenere("Genere " + i);
            libro.setPrezzo(10.0 + i);
            libro.setSconto(5);
            books.add(libro);
        }
        return books;
    }
}
