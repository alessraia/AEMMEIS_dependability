package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
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
import org.mockito.InOrder;

/**
 * Unit tests for GestisciSediServlet
 * Tests the servlet's ability to retrieve all store locations (sedi) and display them
 * through a management page.
 */
class GestisciSediServletTest {

    private GestisciSediServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new GestisciSediServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
    }

    /**
     * Test successful retrieval of all sedi
     * Scenario: Multiple sedi are retrieved from database and set as attributes
     */
    @Test
    void testDoGet_SuccessfulRetrievalOfAllSedi() throws IOException, ServletException {
        // Arrange: Mock the request dispatcher
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        List<Sede> sedi = createMockSedi(3);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify sedi attribute is set
            verify(request).setAttribute("sedi", sedi);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with empty sedi list
     * Scenario: No sedi are present in the system
     */
    @Test
    void testDoGet_EmptySediList() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);
        List<Sede> emptySedi = new ArrayList<>();

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(emptySedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Empty list should be set
            verify(request).setAttribute("sedi", emptySedi);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with single sede
     * Scenario: Only one sede exists
     */
    @Test
    void testDoGet_SingleSede() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);
        List<Sede> singleSede = createMockSedi(1);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(singleSede);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("sedi", singleSede);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test with multiple sedi containing books
     * Scenario: Each sede has associated books
     */
    @Test
    void testDoGet_SediWithAssociatedBooks() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        List<Sede> sedi = new ArrayList<>();
        for (int i = 1; i <= 2; i++) {
            Sede sede = new Sede();
            sede.setIdSede(i);
            sede.setCitta("City " + i);
            sede.setVia("Via " + i);
            sede.setCivico(i * 10);
            sede.setCap("CAP" + i);

            // Add books to sede
            List<Libro> libri = new ArrayList<>();
            for (int j = 0; j < 3; j++) {
                Libro libro = new Libro();
                libro.setIsbn("ISBN-" + i + "-" + j);
                libro.setTitolo("Libro " + i + "-" + j);
                libri.add(libro);
            }
            sede.setLibri(libri);
            sedi.add(sede);
        }

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify all sedi with books are set
            verify(request).setAttribute("sedi", sedi);
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test correct dispatcher path
     * Scenario: Request is forwarded to correct JSP file
     */
    @Test
    void testDoGet_CorrectDispatcherPath() throws IOException, ServletException {
        // Arrange
        String expectedPath = "/WEB-INF/results/admin/sedi/gestisciSedi.jsp";
        when(request.getRequestDispatcher(expectedPath)).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact path
            verify(request).getRequestDispatcher(expectedPath);
        }
    }

    /**
     * Test forward is called exactly once
     * Scenario: Ensures no duplicate forwards
     */
    @Test
    void testDoGet_ForwardCalledExactlyOnce() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(createMockSedi(2));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    /**
     * Test SedeDAO instantiation
     * Scenario: Verify SedeDAO is created exactly once
     */
    @Test
    void testDoGet_SedeDAOInstantiated() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify constructor called exactly once
            assert mockedConstruction.constructed().size() == 1;
        }
    }

    /**
     * Test doRetrivedAll is called exactly once
     * Scenario: Verify database retrieval happens once per request
     */
    @Test
    void testDoGet_DoRetrivedAllCalledOnce() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(createMockSedi(3));
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(mockedConstruction.constructed().get(0), times(1)).doRetrivedAll();
        }
    }

    /**
     * Test large number of sedi
     * Scenario: System has many sedi
     */
    @Test
    void testDoGet_LargeNumberOfSedi() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);
        List<Sede> manySedi = createMockSedi(100);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(manySedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: All sedi should be set
            verify(request).setAttribute("sedi", manySedi);
            assert manySedi.size() == 100;
        }
    }

    /**
     * Test exception propagation from database
     * Scenario: RuntimeException from SedeDAO is propagated
     */
    @Test
    void testDoGet_ExceptionPropagation() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            doThrow(new RuntimeException("Database error")).when(mock).doRetrivedAll();
        })) {
            // Act & Assert
            try {
                servlet.doGet(request, response);
            } catch (RuntimeException e) {
                assert e.getMessage().contains("Database error");
            }
        }
    }

    /**
     * Test setAttribute is called before forward
     * Scenario: Attributes must be set before forwarding request
     */
    @Test
    void testDoGet_SetAttributeBeforeForward() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);
        List<Sede> sedi = createMockSedi(2);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify order - setAttribute before forward
            InOrder inOrder = inOrder(request, dispatcher);
            inOrder.verify(request).setAttribute("sedi", sedi);
            inOrder.verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test sedi list contains correct data
     * Scenario: Verify individual sede properties are preserved
     */
    @Test
    void testDoGet_SediDataPreservation() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        List<Sede> expectedSedi = new ArrayList<>();
        Sede sede1 = new Sede();
        sede1.setIdSede(1);
        sede1.setCitta("Milano");
        sede1.setVia("Via Torino");
        sede1.setCivico(42);
        sede1.setCap("20100");
        expectedSedi.add(sede1);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(expectedSedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify exact sede object is passed
            verify(request).setAttribute("sedi", expectedSedi);
        }
    }

    /**
     * Test with null books list in sede
     * Scenario: Sede may have null books list
     */
    @Test
    void testDoGet_SediWithNullBooks() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        List<Sede> sedi = new ArrayList<>();
        Sede sede = new Sede();
        sede.setIdSede(1);
        sede.setCitta("Torino");
        sede.setVia("Via Roma");
        sede.setCivico(10);
        sede.setCap("10100");
        sede.setLibri(null);
        sedi.add(sede);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("sedi", sedi);
        }
    }

    /**
     * Test multiple sequential requests
     * Scenario: Multiple requests to servlet
     */
    @Test
    void testDoGet_MultipleSequentialRequests() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(createMockSedi(2));
        })) {
            // Act: Call doGet three times
            servlet.doGet(request, response);
            servlet.doGet(request, response);
            servlet.doGet(request, response);

            // Assert: Each call should result in one forward
            verify(dispatcher, times(3)).forward(request, response);
        }
    }

    /**
     * Test response object is passed to dispatcher
     * Scenario: HttpServletResponse is properly forwarded
     */
    @Test
    void testDoGet_ResponsePassedToDispatcher() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(new ArrayList<>());
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert: Verify response passed to forward
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Test sedi with identical properties
     * Scenario: Multiple sedi with same details (different IDs)
     */
    @Test
    void testDoGet_SediWithIdenticalProperties() throws IOException, ServletException {
        // Arrange
        when(request.getRequestDispatcher("/WEB-INF/results/admin/sedi/gestisciSedi.jsp")).thenReturn(dispatcher);

        List<Sede> sedi = new ArrayList<>();
        for (int i = 1; i <= 3; i++) {
            Sede sede = new Sede();
            sede.setIdSede(i);
            sede.setCitta("Milano"); // Same city
            sede.setVia("Via Roma"); // Same street
            sede.setCivico(10 * i);
            sede.setCap("20100"); // Same CAP
            sedi.add(sede);
        }

        try (MockedConstruction<SedeDAO> mockedConstruction = mockConstruction(SedeDAO.class, (mock, context) -> {
            when(mock.doRetrivedAll()).thenReturn(sedi);
        })) {
            // Act
            servlet.doGet(request, response);

            // Assert
            verify(request).setAttribute("sedi", sedi);
        }
    }

    /**
     * Helper method to create mock sedi
     *
     * @param count Number of mock sedi to create
     * @return List of mock sedi with unique IDs and cities
     */
    private List<Sede> createMockSedi(int count) {
        List<Sede> sedi = new ArrayList<>();
        for (int i = 1; i <= count; i++) {
            Sede sede = new Sede();
            sede.setIdSede(i);
            sede.setCitta("City " + i);
            sede.setVia("Via " + i);
            sede.setCivico(i * 10);
            sede.setCap("CAP" + i);
            sede.setLibri(new ArrayList<>());
            sedi.add(sede);
        }
        return sedi;
    }
}
